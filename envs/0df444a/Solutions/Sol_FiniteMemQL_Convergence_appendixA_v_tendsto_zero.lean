-- Prove2me | solution 1 for FiniteMemQL.Convergence.appendixA_v_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T10:12:18.282061+00:00
-- url     : https://prove2.me/submissions/f9042280-8cb8-48e2-b448-b81d0a5e20eb

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting
import Definitions.Def_FiniteMemQL_Convergence_Learning

set_option autoImplicit false
set_option linter.all false

open MeasureTheory ProbabilityTheory Filter Finset Topology
open scoped ENNReal

namespace FiniteMemQL.Convergence.AppAAux

variable {E : Type*} [MeasurableSpace E]

/-- Time-homogeneous step kernels: the next point depends only on the current one. -/
noncomputable def hstep (P : Kernel E E) (n : ℕ) : Kernel (Π _ : Iic n, E) E :=
  P.comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

scoped instance (P : Kernel E E) [IsMarkovKernel P] (n : ℕ) : IsMarkovKernel (hstep P n) := by
  unfold hstep; exact Kernel.IsMarkovKernel.comap _ _

/-- Path law of the homogeneous chain with kernel `P` and initial law `ν`. -/
noncomputable abbrev hpath (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E) :
    Measure (ℕ → E) :=
  Kernel.trajMeasure (X := fun _ => E) ν (hstep P)

lemma lintegral_hpath_zero (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] {F : E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (ω 0) ∂hpath P ν = ∫⁻ z, F z ∂ν := by
  have hlaw : (hpath P ν).map (Preorder.frestrictLe 0) =
      ν.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => E)).symm := by
    rw [hpath, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  have key := lintegral_map (μ := hpath P ν)
    (f := fun h : (Π _ : Iic 0, E) => F (h ⟨0, by simp⟩))
    (hF.comp (measurable_pi_apply _)) (by fun_prop : Measurable (Preorder.frestrictLe 0))
  rw [hlaw, lintegral_map (f := fun h : (Π _ : Iic 0, E) => F (h ⟨0, by simp⟩))
    (hF.comp (measurable_pi_apply _)) (by fun_prop)] at key
  exact key.symm

/-- One-step Markov property of a homogeneous chain. -/
lemma lintegral_hpath_markov (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] (n : ℕ)
    {Φ : (Π _ : Iic n, E) → E → ℝ≥0∞} (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ ω, Φ (Preorder.frestrictLe n ω) (ω (n + 1)) ∂hpath P ν =
      ∫⁻ ω, ∫⁻ z, Φ (Preorder.frestrictLe n ω) z ∂P (ω n) ∂hpath P ν := by
  have hfr : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => E) n) := by fun_prop
  have hc : (hpath P ν).map (Preorder.frestrictLe n) ⊗ₘ hstep P n =
      (hpath P ν).map (fun x => (Preorder.frestrictLe n x, x (n + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  calc ∫⁻ ω, Φ (Preorder.frestrictLe n ω) (ω (n + 1)) ∂hpath P ν
      = ∫⁻ q, Function.uncurry Φ q ∂((hpath P ν).map
          (fun x => (Preorder.frestrictLe n x, x (n + 1)))) :=
        (lintegral_map hΦ (hfr.prodMk (measurable_pi_apply (n + 1)))).symm
    _ = ∫⁻ q, Function.uncurry Φ q ∂((hpath P ν).map (Preorder.frestrictLe n)
          ⊗ₘ hstep P n) := by rw [hc]
    _ = ∫⁻ p, ∫⁻ z, Φ p z ∂hstep P n p ∂((hpath P ν).map (Preorder.frestrictLe n)) :=
        Measure.lintegral_compProd hΦ
    _ = ∫⁻ ω, ∫⁻ z, Φ (Preorder.frestrictLe n ω) z ∂hstep P n (Preorder.frestrictLe n ω)
          ∂hpath P ν :=
        lintegral_map (hΦ.lintegral_kernel_prod_right' (κ := hstep P n)) hfr
    _ = _ := rfl

/-- Extend a finite path on `0..b` by one more point. -/
def extI {b : ℕ} (v : Π _ : Iic b, E) (z : E) : Π _ : Iic (b + 1), E :=
  fun i => if h : i.1 ≤ b then v ⟨i.1, Finset.mem_Iic.mpr h⟩ else z

lemma measurable_extI (b : ℕ) :
    Measurable (fun p : (Π _ : Iic b, E) × E => extI p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i.1 ≤ b
  · simp only [extI, h, dif_pos]; exact (measurable_pi_apply _).comp measurable_fst
  · simp only [extI, h, dif_neg, not_false_eq_true]; exact measurable_snd

lemma extI_eq (b : ℕ) (f : ℕ → E) :
    extI (fun i : Iic b => f i.1) (f (b + 1)) = fun i : Iic (b + 1) => f i.1 := by
  funext i
  by_cases h : i.1 ≤ b
  · simp [extI, h]
  · have hi := Finset.mem_Iic.mp i.2
    have : i.1 = b + 1 := by omega
    simp [extI, h, this]

/-- Finite-dimensional Markov property at time `n`: the path after time `n` is a fresh chain
started at `ω n`, jointly with the past. -/
theorem lintegral_hpath_shift (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] (n : ℕ) : ∀ (b : ℕ)
    (Φ : (Π _ : Iic n, E) → (Π _ : Iic b, E) → ℝ≥0∞), Measurable (Function.uncurry Φ) →
    ∫⁻ ω, Φ (Preorder.frestrictLe n ω) (fun i => ω (n + i.1)) ∂hpath P ν =
      ∫⁻ ω, ∫⁻ ω', Φ (Preorder.frestrictLe n ω) (Preorder.frestrictLe b ω')
        ∂hpath P (Measure.dirac (ω n)) ∂hpath P ν := by
  intro b
  induction b with
  | zero =>
    intro Φ hΦ
    refine lintegral_congr fun ω => ?_
    have h0 : ∀ g : ℕ → E, (fun i : Iic 0 => g i.1) = fun _ => g 0 := by
      intro g; funext i
      obtain ⟨i, hi⟩ := i
      have : i = 0 := by simpa using hi
      subst this; rfl
    have hF : Measurable (fun z : E => Φ (Preorder.frestrictLe n ω) (fun _ : Iic 0 => z)) :=
      hΦ.comp (measurable_const.prodMk (measurable_pi_lambda _ fun _ => measurable_id))
    have e1 : (fun i : Iic 0 => ω (n + i.1)) = fun _ => ω n := by
      simpa using h0 (fun k => ω (n + k))
    rw [e1]
    calc Φ (Preorder.frestrictLe n ω) (fun _ => ω n)
        = ∫⁻ z, Φ (Preorder.frestrictLe n ω) (fun _ : Iic 0 => z) ∂Measure.dirac (ω n) :=
          (lintegral_dirac' _ hF).symm
      _ = ∫⁻ ω', Φ (Preorder.frestrictLe n ω) (fun _ : Iic 0 => ω' 0)
            ∂hpath P (Measure.dirac (ω n)) := (lintegral_hpath_zero P _ hF).symm
      _ = _ := by
          refine lintegral_congr fun ω' => ?_
          congr 1
          exact (h0 ω').symm
  | succ b ih =>
    intro Φ hΦ
    have hn : ∀ j : Iic n, j.1 ∈ Iic (n + b) := fun j =>
      Finset.mem_Iic.mpr (by have := Finset.mem_Iic.mp j.2; omega)
    have hb : ∀ i : Iic b, n + i.1 ∈ Iic (n + b) := fun i =>
      Finset.mem_Iic.mpr (by have := Finset.mem_Iic.mp i.2; omega)
    -- the integrand as a function of the path up to `n + b` and the point at `n + b + 1`
    let Ψ : (Π _ : Iic (n + b), E) → E → ℝ≥0∞ := fun r z =>
      Φ (fun j => r ⟨j.1, hn j⟩) (extI (fun i : Iic b => r ⟨n + i.1, hb i⟩) z)
    have hΨ : Measurable (Function.uncurry Ψ) := by
      have h1 : Measurable (fun q : (Π _ : Iic (n + b), E) × E =>
          (fun j : Iic n => q.1 ⟨j.1, hn j⟩ : Π _ : Iic n, E)) :=
        measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_fst
      have h2 : Measurable (fun q : (Π _ : Iic (n + b), E) × E =>
          ((fun i : Iic b => q.1 ⟨n + i.1, hb i⟩ : Π _ : Iic b, E), q.2)) :=
        (measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_fst).prodMk
          measurable_snd
      exact hΦ.comp (h1.prodMk ((measurable_extI b).comp h2))
    let Φ' : (Π _ : Iic n, E) → (Π _ : Iic b, E) → ℝ≥0∞ := fun a v =>
      ∫⁻ z, Φ a (extI v z) ∂P (v ⟨b, Finset.mem_Iic.mpr le_rfl⟩)
    have hΦ' : Measurable (Function.uncurry Φ') := by
      have hk : Measurable (fun p : (Π _ : Iic n, E) × (Π _ : Iic b, E) =>
          p.2 ⟨b, Finset.mem_Iic.mpr le_rfl⟩) := (measurable_pi_apply _).comp measurable_snd
      have hf : Measurable (fun q : ((Π _ : Iic n, E) × (Π _ : Iic b, E)) × E =>
          Φ q.1.1 (extI q.1.2 q.2)) :=
        hΦ.comp ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_extI b).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      exact hf.lintegral_kernel_prod_right' (κ := P.comap _ hk)
    have hL : ∀ ω : ℕ → E, Φ (Preorder.frestrictLe n ω) (fun i => ω (n + i.1)) =
        Ψ (Preorder.frestrictLe (n + b) ω) (ω (n + b + 1)) := by
      intro ω
      have := extI_eq b (fun k => ω (n + k))
      simp only [show n + (b + 1) = n + b + 1 by omega] at this
      simp only [Ψ, Preorder.frestrictLe, Finset.restrict]
      rw [this]
      rfl
    calc ∫⁻ ω, Φ (Preorder.frestrictLe n ω) (fun i => ω (n + i.1)) ∂hpath P ν
        = ∫⁻ ω, Ψ (Preorder.frestrictLe (n + b) ω) (ω (n + b + 1)) ∂hpath P ν :=
          lintegral_congr fun ω => hL ω
      _ = ∫⁻ ω, ∫⁻ z, Ψ (Preorder.frestrictLe (n + b) ω) z ∂P (ω (n + b)) ∂hpath P ν :=
          lintegral_hpath_markov P ν (n + b) hΨ
      _ = ∫⁻ ω, Φ' (Preorder.frestrictLe n ω) (fun i => ω (n + i.1)) ∂hpath P ν := rfl
      _ = ∫⁻ ω, ∫⁻ ω', Φ' (Preorder.frestrictLe n ω) (Preorder.frestrictLe b ω')
            ∂hpath P (Measure.dirac (ω n)) ∂hpath P ν := ih Φ' hΦ'
      _ = _ := by
          refine lintegral_congr fun ω => ?_
          have hg : Measurable (Function.uncurry
              (fun (r : Π _ : Iic b, E) (z : E) => Φ (Preorder.frestrictLe n ω) (extI r z))) :=
            hΦ.comp (measurable_const.prodMk (measurable_extI b))
          have hm := lintegral_hpath_markov P (Measure.dirac (ω n)) b hg
          refine Eq.trans (b := ∫⁻ ω', ∫⁻ z, Φ (Preorder.frestrictLe n ω)
            (extI (Preorder.frestrictLe b ω') z) ∂P (ω' b) ∂hpath P (Measure.dirac (ω n))) rfl ?_
          rw [← hm]
          refine lintegral_congr fun ω' => ?_
          exact congrArg (Φ (Preorder.frestrictLe n ω)) (extI_eq b ω')

/-- The chain started at a point, as a kernel from paths up to time `n` (started at the last point). -/
noncomputable def shiftK (P : Kernel E E) [IsMarkovKernel P] (n : ℕ) :
    Kernel (Π _ : Iic n, E) (ℕ → E) :=
  (Kernel.traj (X := fun _ => E) (hstep P) 0).comap
    (fun a => (MeasurableEquiv.piUnique (fun _ : Iic 0 => E)).symm (a ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
    (by fun_prop)

scoped instance (P : Kernel E E) [IsMarkovKernel P] (n : ℕ) : IsMarkovKernel (shiftK P n) := by
  unfold shiftK; exact Kernel.IsMarkovKernel.comap _ _

lemma shiftK_apply (P : Kernel E E) [IsMarkovKernel P] (n : ℕ) (a : Π _ : Iic n, E) :
    shiftK P n a = hpath P (Measure.dirac (a ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) := by
  unfold shiftK
  rw [Kernel.comap_apply, hpath, Kernel.trajMeasure]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (MeasurableEquiv.measurable _)]
  exact (lintegral_dirac' _ ((Kernel.measurable_coe _ hs).comp (MeasurableEquiv.measurable _))).symm

/-- Markov property at time `n`, measure form: the joint law of the past up to `n` and the
shifted path is the past composed with the chain restarted at `ω n`. -/
theorem map_hpath_shift (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (hpath P ν).map (fun ω => (Preorder.frestrictLe n ω, fun t => ω (n + t))) =
      ((hpath P ν).map (Preorder.frestrictLe n)) ⊗ₘ shiftK P n := by
  have hg : Measurable (fun ω : ℕ → E => (Preorder.frestrictLe n ω, fun t => ω (n + t))) :=
    (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_lambda _ fun t => measurable_pi_apply _)
  have hfr : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => E) n) := by fun_prop
  let C : Set (Set ((Π _ : Iic n, E) × (ℕ → E))) := {S | ∃ b : ℕ, ∃ T, MeasurableSet T ∧
    S = Prod.map id (Preorder.frestrictLe (π := fun _ : ℕ => E) b) ⁻¹' T}
  haveI : IsProbabilityMeasure ((hpath P ν).map (Preorder.frestrictLe n)) :=
    Measure.isProbabilityMeasure_map hfr.aemeasurable
  haveI : IsProbabilityMeasure ((hpath P ν).map
      (fun ω => (Preorder.frestrictLe n ω, fun t => ω (n + t)))) :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  refine ext_of_generate_finite C ?_ ?_ ?_ (by simp [measure_univ])
  · refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
    · refine sup_le ?_ ?_
      · have : @Measurable _ _ (MeasurableSpace.generateFrom C) _ Prod.fst := by
          intro A hA
          exact MeasurableSpace.measurableSet_generateFrom ⟨0, A ×ˢ Set.univ,
            hA.prod MeasurableSet.univ, by ext p; simp⟩
        exact this.comap_le
      · have : @Measurable _ _ (MeasurableSpace.generateFrom C) _ Prod.snd := by
          rw [@measurable_pi_iff]
          intro i B hB
          exact MeasurableSpace.measurableSet_generateFrom ⟨i,
            Set.univ ×ˢ ((fun v : Π _ : Iic i, E => v ⟨i, Finset.mem_Iic.mpr le_rfl⟩) ⁻¹' B),
            MeasurableSet.univ.prod (measurable_pi_apply _ hB), by ext p; simp [Preorder.frestrictLe]⟩
        exact this.comap_le
    · rintro S ⟨b, T, hT, rfl⟩
      exact (measurable_id.prodMap (Preorder.measurable_frestrictLe (X := fun _ : ℕ => E) b)) hT
  · rintro S1 ⟨b1, T1, hT1, rfl⟩ S2 ⟨b2, T2, hT2, rfl⟩ _
    refine ⟨max b1 b2, Prod.map id (Preorder.frestrictLe₂ (π := fun _ : ℕ => E)
        (le_max_left b1 b2)) ⁻¹' T1 ∩
      Prod.map id (Preorder.frestrictLe₂ (π := fun _ : ℕ => E) (le_max_right b1 b2)) ⁻¹' T2,
      ((measurable_id.prodMap (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => E) _)) hT1).inter
        ((measurable_id.prodMap (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => E) _)) hT2), rfl⟩
  · rintro S ⟨b, T, hT, rfl⟩
    have hS := (measurable_id.prodMap (Preorder.measurable_frestrictLe (X := fun _ : ℕ => E) b)) hT
    let Φ : (Π _ : Iic n, E) → (Π _ : Iic b, E) → ℝ≥0∞ := fun a v => T.indicator 1 (a, v)
    have hΦ : Measurable (Function.uncurry Φ) := measurable_one.indicator hT
    have h := lintegral_hpath_shift P ν n b Φ hΦ
    rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS,
      lintegral_map (measurable_one.indicator hS) hg,
      Measure.lintegral_compProd (measurable_one.indicator hS),
      lintegral_map ((measurable_one.indicator hS).lintegral_kernel_prod_right'
        (κ := shiftK P n)) hfr]
    refine Eq.trans ?_ (h.trans ?_)
    · refine lintegral_congr fun ω => ?_
      simp only [Φ, Set.indicator_apply, Set.mem_preimage]
      rfl
    · refine lintegral_congr fun ω => ?_
      rw [shiftK_apply]
      refine lintegral_congr fun ω' => ?_
      simp only [Φ, Set.indicator_apply, Set.mem_preimage]
      rfl

/-- Markov property at time `n` for every measurable functional of the past and the future. -/
theorem lintegral_hpath_shift_full (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] (n : ℕ) {F : (Π _ : Iic n, E) × (ℕ → E) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (Preorder.frestrictLe n ω, fun t => ω (n + t)) ∂hpath P ν =
      ∫⁻ ω, ∫⁻ ω', F (Preorder.frestrictLe n ω, ω') ∂hpath P (Measure.dirac (ω n)) ∂hpath P ν := by
  have hg : Measurable (fun ω : ℕ → E => (Preorder.frestrictLe n ω, fun t => ω (n + t))) :=
    (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_lambda _ fun t => measurable_pi_apply _)
  have hfr : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => E) n) := by fun_prop
  rw [← lintegral_map hF hg, map_hpath_shift, Measure.lintegral_compProd hF,
    lintegral_map (hF.lintegral_kernel_prod_right' (κ := shiftK P n)) hfr]
  refine lintegral_congr fun ω => ?_
  rw [shiftK_apply]
  rfl

lemma chainLaw_eq_hpath (P : Kernel E E) [IsMarkovKernel P] (x : E) :
    RiskSensMDP.AverageCost.chainLaw P x = hpath P (Measure.dirac x) := rfl

/-- One-step martingale identity on `piLE n`-cylinders for a nonnegative harmonic `h`. -/
lemma setIntegral_harm_step (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] {h : E → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    (hharm : ∀ x, ∫⁻ y, ENNReal.ofReal (h y) ∂P x = ENNReal.ofReal (h x)) (n : ℕ)
    {t : Set (Π _ : Iic n, E)} (ht : MeasurableSet t) :
    ∫ ω in Preorder.frestrictLe n ⁻¹' t, h (ω (n + 1)) ∂hpath P ν =
      ∫ ω in Preorder.frestrictLe n ⁻¹' t, h (ω n) ∂hpath P ν := by
  have hfr : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => E) n) := by fun_prop
  have hS : MeasurableSet (Preorder.frestrictLe (π := fun _ : ℕ => E) n ⁻¹' t) := hfr ht
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => h0 _)
      ((hm.comp (measurable_pi_apply _)).aestronglyMeasurable),
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => h0 _)
      ((hm.comp (measurable_pi_apply _)).aestronglyMeasurable)]
  congr 1
  rw [← lintegral_indicator hS, ← lintegral_indicator hS]
  have e1 : ∀ (m : ℕ) (ω : ℕ → E), (Preorder.frestrictLe n ⁻¹' t).indicator
      (fun ω : ℕ → E => ENNReal.ofReal (h (ω m))) ω =
      t.indicator (fun _ => (1 : ℝ≥0∞)) (Preorder.frestrictLe n ω) * ENNReal.ofReal (h (ω m)) := by
    intro m ω
    by_cases hω : Preorder.frestrictLe n ω ∈ t
    · simp only [Set.indicator, Set.mem_preimage, hω, if_true, one_mul]
    · simp only [Set.indicator, Set.mem_preimage, hω, if_false, zero_mul]
  have key := lintegral_hpath_markov P ν n
    (Φ := fun a z => t.indicator (fun _ => (1 : ℝ≥0∞)) a * ENNReal.ofReal (h z))
    (by
      apply Measurable.mul
      · exact (measurable_const.indicator ht).comp measurable_fst
      · exact ENNReal.measurable_ofReal.comp (hm.comp measurable_snd))
  calc ∫⁻ ω, (Preorder.frestrictLe n ⁻¹' t).indicator
          (fun ω : ℕ → E => ENNReal.ofReal (h (ω (n + 1)))) ω ∂hpath P ν
      = ∫⁻ ω, t.indicator (fun _ => (1 : ℝ≥0∞)) (Preorder.frestrictLe n ω) *
          ENNReal.ofReal (h (ω (n + 1))) ∂hpath P ν := lintegral_congr fun ω => e1 (n + 1) ω
    _ = ∫⁻ ω, ∫⁻ z, t.indicator (fun _ => (1 : ℝ≥0∞)) (Preorder.frestrictLe n ω) *
          ENNReal.ofReal (h z) ∂P (ω n) ∂hpath P ν := key
    _ = ∫⁻ ω, t.indicator (fun _ => (1 : ℝ≥0∞)) (Preorder.frestrictLe n ω) *
          ENNReal.ofReal (h (ω n)) ∂hpath P ν := by
        refine lintegral_congr fun ω => ?_
        rw [lintegral_const_mul _ hm.ennreal_ofReal, hharm]
    _ = _ := (lintegral_congr fun ω => e1 n ω).symm

lemma harm_integrable (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] {h : E → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    {B : ℝ} (hB : ∀ x, h x ≤ B) (n : ℕ) :
    Integrable (fun ω : ℕ → E => h (ω n)) (hpath P ν) :=
  (integrable_const B).mono' (hm.comp (measurable_pi_apply n)).aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hB _)

/-- A nonnegative bounded harmonic function along the chain is a martingale. -/
lemma harm_martingale (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] {h : E → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    {B : ℝ} (hB : ∀ x, h x ≤ B)
    (hharm : ∀ x, ∫⁻ y, ENNReal.ofReal (h y) ∂P x = ENNReal.ofReal (h x)) :
    Martingale (fun n (ω : ℕ → E) => h (ω n)) (Filtration.piLE (X := fun _ : ℕ => E))
      (hpath P ν) := by
  have hadp : StronglyAdapted (Filtration.piLE (X := fun _ : ℕ => E))
      (fun n (ω : ℕ → E) => h (ω n)) := by
    intro n
    rw [Filtration.piLE_eq_comap_frestrictLe]
    exact ((hm.comp (measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Iic n))).comp
      (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ => E) n))).stronglyMeasurable
  refine martingale_nat hadp (harm_integrable P ν hm h0 hB) fun n => ?_
  refine ae_eq_condExp_of_forall_setIntegral_eq ((Filtration.piLE (X := fun _ : ℕ => E)).le n)
    (harm_integrable P ν hm h0 hB (n + 1))
    (fun s _ _ => (harm_integrable P ν hm h0 hB n).integrableOn) ?_ (hadp n).aestronglyMeasurable
  rw [Filtration.piLE_eq_comap_frestrictLe]
  rintro - ⟨t, ht, rfl⟩ -
  exact (setIntegral_harm_step P ν hm h0 hharm n ht).symm

/-- Martingale convergence for a bounded harmonic function started at `x`. -/
lemma harm_tendsto (P : Kernel E E) [IsMarkovKernel P] (x : E)
    {h : E → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) {B : ℝ} (hB : ∀ x, h x ≤ B)
    (hharm : ∀ x, ∫⁻ y, ENNReal.ofReal (h y) ∂P x = ENNReal.ofReal (h x)) :
    ∃ H : (ℕ → E) → ℝ, Integrable H (hpath P (Measure.dirac x)) ∧
      (∀ᵐ ω ∂hpath P (Measure.dirac x), Tendsto (fun n => h (ω n)) atTop (𝓝 (H ω))) ∧
      ∫ ω, H ω ∂hpath P (Measure.dirac x) = h x := by
  have hM := harm_martingale P (Measure.dirac x) hm h0 hB hharm
  have hbdd : ∀ n, eLpNorm (fun ω : ℕ → E => h (ω n)) 1 (hpath P (Measure.dirac x)) ≤
      ENNReal.ofReal B := by
    intro n
    calc eLpNorm (fun ω : ℕ → E => h (ω n)) 1 (hpath P (Measure.dirac x))
        ≤ (hpath P (Measure.dirac x)) Set.univ ^ (ENNReal.toReal 1)⁻¹ * ENNReal.ofReal B :=
          eLpNorm_le_of_ae_bound (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hB _)
      _ = ENNReal.ofReal B := by simp [measure_univ]
  have hconv := hM.submartingale.ae_tendsto_limitProcess hbdd
  have hint := memLp_one_iff_integrable.mp (hM.submartingale.memLp_limitProcess hbdd)
  refine ⟨_, hint, hconv, ?_⟩
  have hconst : ∀ n, ∫ ω, h (ω n) ∂hpath P (Measure.dirac x) = h x := by
    intro n
    have e := hM.setIntegral_eq (Nat.zero_le n) (MeasurableSet.univ)
    rw [setIntegral_univ, setIntegral_univ] at e
    rw [← e, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => h0 _)
      ((hm.comp (measurable_pi_apply _)).aestronglyMeasurable),
      lintegral_hpath_zero P _ hm.ennreal_ofReal,
      lintegral_dirac' _ hm.ennreal_ofReal, ENNReal.toReal_ofReal (h0 x)]
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun n (ω : ℕ → E) => h (ω n)) (fun _ => B)
    (fun n => (hm.comp (measurable_pi_apply n)).aestronglyMeasurable) (integrable_const B)
    (fun n => ae_of_all _ fun ω => by
      show ‖h (ω n)‖ ≤ B
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hB _) hconv
  simp only [hconst] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

lemma measurableSet_frequently_mem {B : Set E} (hB : MeasurableSet B) :
    MeasurableSet {ω : ℕ → E | ∃ᶠ n in atTop, ω n ∈ B} := by
  simp_rw [Filter.frequently_atTop]
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun N => ?_
  rw [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun n => ?_
  rw [Set.ofPred_and]
  exact (MeasurableSet.const _).inter (measurable_pi_apply n hB)

/-- Harris recurrence in almost-everywhere form. -/
lemma harris_ae {P : Kernel E E} [IsMarkovKernel P] {φ : Measure E}
    (hφ : ∀ B : Set E, MeasurableSet B → 0 < φ B → ∀ x : E,
      RiskSensMDP.AverageCost.chainLaw P x {ω | ∃ᶠ n in atTop, ω n ∈ B} = 1)
    {B : Set E} (hB : MeasurableSet B) (hpos : 0 < φ B) (x : E) :
    ∀ᵐ ω ∂hpath P (Measure.dirac x), ∃ᶠ n in atTop, ω n ∈ B :=
  (ae_iff_measure_eq (measurableSet_frequently_mem hB).nullMeasurableSet).mpr
    (by rw [measure_univ, ← chainLaw_eq_hpath, hφ B hB hpos x])

/-- **H3** (Meyn–Tweedie Thm 17.1.5): under Harris recurrence every bounded nonnegative
harmonic function is constant. -/
theorem harm_const (P : Kernel E E) [IsMarkovKernel P]
    (hH : RiskSensMDP.AverageCost.IsHarrisRecurrent P)
    {h : E → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) {B : ℝ} (hB : ∀ x, h x ≤ B)
    (hharm : ∀ x, ∫⁻ y, ENNReal.ofReal (h y) ∂P x = ENNReal.ofReal (h x)) (x y : E) :
    h x = h y := by
  obtain ⟨φ, -, hφ0, hφ⟩ := hH
  have hlt : ∀ a : ℝ, MeasurableSet {z | h z < a} := fun a => measurableSet_lt hm measurable_const
  have hgt : ∀ a : ℝ, MeasurableSet {z | a < h z} := fun a => measurableSet_lt measurable_const hm
  have hle : ∀ a : ℝ, MeasurableSet {z | a ≤ h z} := fun a => measurableSet_le measurable_const hm
  have hge : ∀ a : ℝ, MeasurableSet {z | h z ≤ a} := fun a => measurableSet_le hm measurable_const
  have hφpos : 0 < φ Set.univ := by
    rw [pos_iff_ne_zero]; exact fun h' => hφ0 (Measure.measure_univ_eq_zero.mp h')
  -- lower bound: if `{h < a}` is `φ`-null then `a ≤ h z`
  have lower : ∀ a : ℝ, φ {z | h z < a} = 0 → ∀ z, a ≤ h z := by
    intro a hnull z
    have hpos : 0 < φ {z | a ≤ h z} := by
      have : φ Set.univ ≤ φ {z | h z < a} + φ {z | a ≤ h z} := by
        calc φ Set.univ = φ ({z | h z < a} ∪ {z | a ≤ h z}) := by
              congr 1; ext w; simp [lt_or_ge]
          _ ≤ _ := measure_union_le _ _
      rw [hnull, zero_add] at this
      exact lt_of_lt_of_le hφpos this
    obtain ⟨H, hHi, hHt, hHe⟩ := harm_tendsto P z hm h0 hB hharm
    have hae : ∀ᵐ ω ∂hpath P (Measure.dirac z), a ≤ H ω := by
      filter_upwards [harris_ae hφ (hle a) hpos z, hHt] with ω hf ht
      by_contra hc
      push Not at hc
      obtain ⟨n, h1, h2⟩ := (hf.and_eventually (ht.eventually_lt_const hc)).exists
      exact lt_irrefl _ (lt_of_le_of_lt h1 h2)
    rw [← hHe]
    have := integral_mono_ae (integrable_const a) hHi hae
    simpa [measure_univ] using this
  have upper : ∀ b : ℝ, φ {z | b < h z} = 0 → ∀ z, h z ≤ b := by
    intro b hnull z
    have hpos : 0 < φ {z | h z ≤ b} := by
      have : φ Set.univ ≤ φ {z | b < h z} + φ {z | h z ≤ b} := by
        calc φ Set.univ = φ ({z | b < h z} ∪ {z | h z ≤ b}) := by
              congr 1; ext w; simp [lt_or_ge]
          _ ≤ _ := measure_union_le _ _
      rw [hnull, zero_add] at this
      exact lt_of_lt_of_le hφpos this
    obtain ⟨H, hHi, hHt, hHe⟩ := harm_tendsto P z hm h0 hB hharm
    have hae : ∀ᵐ ω ∂hpath P (Measure.dirac z), H ω ≤ b := by
      filter_upwards [harris_ae hφ (hge b) hpos z, hHt] with ω hf ht
      by_contra hc
      push Not at hc
      obtain ⟨n, h1, h2⟩ := (hf.and_eventually (ht.eventually_const_lt hc)).exists
      exact lt_irrefl _ (lt_of_le_of_lt h1 h2)
    rw [← hHe]
    have := integral_mono_ae hHi (integrable_const b) hae
    simpa [measure_univ] using this
  -- no oscillation
  have nosc : ∀ a b : ℝ, a < b → φ {z | h z < a} = 0 ∨ φ {z | b < h z} = 0 := by
    intro a b hab
    by_contra hc
    push Not at hc
    obtain ⟨ha, hb⟩ := hc
    obtain ⟨H, -, hHt, -⟩ := harm_tendsto P x hm h0 hB hharm
    have hall : ∀ᵐ ω ∂hpath P (Measure.dirac x), False := by
      filter_upwards [harris_ae hφ (hlt a) (pos_iff_ne_zero.mpr ha) x,
        harris_ae hφ (hgt b) (pos_iff_ne_zero.mpr hb) x, hHt] with ω f1 f2 ht
      rcases lt_or_ge (H ω) b with hc | hc
      · obtain ⟨n, h1, h2⟩ := (f2.and_eventually (ht.eventually_lt_const hc)).exists
        exact lt_irrefl _ (lt_trans h1 h2)
      · have hc' : a < H ω := lt_of_lt_of_le hab hc
        obtain ⟨n, h1, h2⟩ := (f1.and_eventually (ht.eventually_const_lt hc')).exists
        exact lt_irrefl _ (lt_trans h1 h2)
    exact IsProbabilityMeasure.ne_zero (hpath P (Measure.dirac x)) (by simpa using hall)
  have key : ∀ u v : E, h u < h v → False := by
    intro u v huv
    have hab : h u + (h v - h u) / 3 < h u + 2 * (h v - h u) / 3 := by linarith
    rcases nosc _ _ hab with h1 | h1
    · have := lower _ h1 u; linarith
    · have := upper _ h1 v; linarith
  rcases lt_trichotomy (h x) (h y) with c | c | c
  · exact (key x y c).elim
  · exact c
  · exact (key y x c).elim


/-! ### H4: shift-invariant events -/

lemma measurable_lintegral_hpath_dirac (P : Kernel E E) [IsMarkovKernel P]
    {F : (ℕ → E) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun z : E => ∫⁻ ω, F ω ∂hpath P (Measure.dirac z) := by
  have hc : Measurable (fun z : E => (fun _ : Iic 0 => z)) :=
    measurable_pi_lambda _ fun _ => measurable_id
  have := (hF.lintegral_kernel (κ := shiftK P 0)).comp hc
  simpa only [Function.comp_def, shiftK_apply] using this

lemma measurable_hpath_dirac (P : Kernel E E) [IsMarkovKernel P] {s : Set (ℕ → E)}
    (hs : MeasurableSet s) : Measurable fun z : E => hpath P (Measure.dirac z) s := by
  have := measurable_lintegral_hpath_dirac P (measurable_one.indicator hs : Measurable (s.indicator (1 : (ℕ → E) → ℝ≥0∞)))
  simpa only [lintegral_indicator_one hs] using this

/-- The path law from `ν` is the mixture of the path laws from points. -/
lemma lintegral_hpath_bind (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] {F : (ℕ → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F ω ∂hpath P ν = ∫⁻ z, ∫⁻ ω, F ω ∂hpath P (Measure.dirac z) ∂ν := by
  have h1 := lintegral_hpath_shift_full P ν 0 (F := fun q => F q.2) (hF.comp measurable_snd)
  simp only [zero_add] at h1
  rw [h1, lintegral_hpath_zero P ν (measurable_lintegral_hpath_dirac P hF)]

lemma inv_iter {L : Set (ℕ → E)} (hinv : ∀ ω : ℕ → E, (fun t => ω (1 + t)) ∈ L ↔ ω ∈ L)
    (n : ℕ) (ω : ℕ → E) : (fun t => ω (n + t)) ∈ L ↔ ω ∈ L := by
  induction n with
  | zero => rw [show (fun t => ω (0 + t)) = ω from funext fun t => by rw [zero_add]]
  | succ n ih =>
    rw [← ih, ← hinv (fun t => ω (n + t))]
    have : (fun t => ω (n + 1 + t)) = (fun t => (fun t => ω (n + t)) (1 + t)) := by
      funext t; congr 1; omega
    rw [this]

/-- For a shift-invariant event, `z ↦ P_z(L)` is harmonic. -/
lemma harm_of_shift_invariant (P : Kernel E E) [IsMarkovKernel P] {L : Set (ℕ → E)}
    (hL : MeasurableSet L) (hinv : ∀ ω : ℕ → E, (fun t => ω (1 + t)) ∈ L ↔ ω ∈ L) (z : E) :
    ∫⁻ y, hpath P (Measure.dirac y) L ∂P z = hpath P (Measure.dirac z) L := by
  have hF : Measurable (fun q : (Π _ : Iic 1, E) × (ℕ → E) => L.indicator (1 : (ℕ → E) → ℝ≥0∞) q.2) :=
    (measurable_const.indicator hL).comp measurable_snd
  have h1 : ∫⁻ ω, L.indicator (1 : (ℕ → E) → ℝ≥0∞) ω ∂hpath P (Measure.dirac z) =
      ∫⁻ ω, ∫⁻ ω', L.indicator (1 : (ℕ → E) → ℝ≥0∞) ω' ∂hpath P (Measure.dirac (ω 1))
        ∂hpath P (Measure.dirac z) := by
    refine (lintegral_congr fun ω => ?_).trans (lintegral_hpath_shift_full P _ 1 hF)
    show L.indicator (1 : (ℕ → E) → ℝ≥0∞) ω = L.indicator 1 (fun t => ω (1 + t))
    by_cases h : ω ∈ L
    · simp only [Set.indicator_of_mem h, Set.indicator_of_mem ((hinv ω).2 h), Pi.one_apply]
    · simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hinv ω).1 h'))]
  simp only [lintegral_indicator_one hL] at h1
  rw [h1]
  have h2 := lintegral_hpath_markov P (Measure.dirac z) 0
    (Φ := fun _ y => hpath P (Measure.dirac y) L) ((measurable_hpath_dirac P hL).comp measurable_snd)
  simp only [zero_add] at h2
  rw [h2, lintegral_hpath_zero P _ (measurable_hpath_dirac P hL).lintegral_kernel,
    lintegral_dirac' _ (measurable_hpath_dirac P hL).lintegral_kernel]

lemma hpath_cyl_inter (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] {L : Set (ℕ → E)} (hL : MeasurableSet L)
    (hinv : ∀ ω : ℕ → E, (fun t => ω (1 + t)) ∈ L ↔ ω ∈ L) {c : ℝ≥0∞}
    (hc : ∀ z, hpath P (Measure.dirac z) L = c) (n : ℕ) {t : Set (Π _ : Iic n, E)}
    (ht : MeasurableSet t) :
    hpath P ν (Preorder.frestrictLe n ⁻¹' t ∩ L) = c * hpath P ν (Preorder.frestrictLe n ⁻¹' t) := by
  have hfr : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => E) n) := by fun_prop
  have hF : Measurable (fun q : (Π _ : Iic n, E) × (ℕ → E) =>
      t.indicator (1 : (Π _ : Iic n, E) → ℝ≥0∞) q.1 * L.indicator (1 : (ℕ → E) → ℝ≥0∞) q.2) :=
    ((measurable_const.indicator ht).comp measurable_fst).mul
      ((measurable_const.indicator hL).comp measurable_snd)
  have e : ∀ ω : ℕ → E, (Preorder.frestrictLe n ⁻¹' t ∩ L).indicator (1 : (ℕ → E) → ℝ≥0∞) ω =
      t.indicator (1 : (Π _ : Iic n, E) → ℝ≥0∞) (Preorder.frestrictLe n ω) *
        L.indicator (1 : (ℕ → E) → ℝ≥0∞) (fun t => ω (n + t)) := by
    intro ω
    by_cases h1 : Preorder.frestrictLe n ω ∈ t <;> by_cases h2 : ω ∈ L <;>
      simp [Set.indicator, h1, h2, inv_iter hinv n ω]
  have h1 : ∫⁻ ω, (Preorder.frestrictLe n ⁻¹' t ∩ L).indicator (1 : (ℕ → E) → ℝ≥0∞) ω ∂hpath P ν =
      ∫⁻ ω, ∫⁻ ω', t.indicator (1 : (Π _ : Iic n, E) → ℝ≥0∞) (Preorder.frestrictLe n ω) *
        L.indicator (1 : (ℕ → E) → ℝ≥0∞) ω' ∂hpath P (Measure.dirac (ω n)) ∂hpath P ν :=
    (lintegral_congr fun ω => e ω).trans (lintegral_hpath_shift_full P ν n hF)
  rw [← lintegral_indicator_one ((hfr ht).inter hL), h1]
  calc ∫⁻ ω, ∫⁻ ω', t.indicator (1 : (Π _ : Iic n, E) → ℝ≥0∞) (Preorder.frestrictLe n ω) *
        L.indicator (1 : (ℕ → E) → ℝ≥0∞) ω' ∂hpath P (Measure.dirac (ω n)) ∂hpath P ν
      = ∫⁻ ω, (Preorder.frestrictLe n ⁻¹' t).indicator (1 : (ℕ → E) → ℝ≥0∞) ω * c ∂hpath P ν := by
        refine lintegral_congr fun ω => ?_
        rw [lintegral_const_mul _ (measurable_one.indicator hL), lintegral_indicator_one hL, hc]
        rfl
    _ = c * hpath P ν (Preorder.frestrictLe n ⁻¹' t) := by
        rw [lintegral_mul_const _ (measurable_one.indicator (hfr ht)),
          lintegral_indicator_one (hfr ht), mul_comm]

/-- Zero-one law: a shift-invariant event with constant hitting law has probability 0 or 1. -/
theorem invariant_zero_one (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] {L : Set (ℕ → E)} (hL : MeasurableSet L)
    (hinv : ∀ ω : ℕ → E, (fun t => ω (1 + t)) ∈ L ↔ ω ∈ L) {c : ℝ≥0∞}
    (hc : ∀ z, hpath P (Measure.dirac z) L = c) : c = 0 ∨ c = 1 := by
  have h0 := hpath_cyl_inter P ν hL hinv hc 0 (t := Set.univ) MeasurableSet.univ
  rw [Set.preimage_univ, Set.univ_inter, measure_univ, mul_one] at h0
  have hcT : c ≠ ⊤ := by rw [← h0]; exact measure_ne_top _ _
  have hfi : Integrable (L.indicator (1 : (ℕ → E) → ℝ)) (hpath P ν) :=
    (integrable_const (1 : ℝ)).indicator hL
  have hsup : (MeasurableSpace.pi : MeasurableSpace (ℕ → E)) ≤
      ⨆ n, Filtration.piLE (X := fun _ : ℕ => E) n := by
    refine iSup_le fun i => le_iSup_of_le i ?_
    rw [Filtration.piLE_eq_comap_frestrictLe]
    exact ((measurable_pi_apply (⟨i, Finset.mem_Iic.mpr le_rfl⟩ : Iic i)).comp
      (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ => E) i))).comap_le
  have hfm : StronglyMeasurable[⨆ n, Filtration.piLE (X := fun _ : ℕ => E) n]
      (L.indicator (1 : (ℕ → E) → ℝ)) :=
    (measurable_const.indicator hL).stronglyMeasurable.mono hsup
  have hce : ∀ n, (hpath P ν)[L.indicator (1 : (ℕ → E) → ℝ) | Filtration.piLE n] =ᵐ[hpath P ν]
      fun _ => c.toReal := by
    intro n
    refine (ae_eq_condExp_of_forall_setIntegral_eq ((Filtration.piLE (X := fun _ : ℕ => E)).le n)
      hfi (fun s _ _ => (integrable_const _).integrableOn) ?_
      stronglyMeasurable_const.aestronglyMeasurable).symm
    rw [Filtration.piLE_eq_comap_frestrictLe]
    rintro - ⟨t, ht, rfl⟩ -
    rw [setIntegral_const, setIntegral_indicator hL]
    simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    rw [hpath_cyl_inter P ν hL hinv hc n ht, ENNReal.toReal_mul, mul_comm]
  have hlev := Integrable.tendsto_ae_condExp (ℱ := Filtration.piLE (X := fun _ : ℕ => E)) hfi hfm
  have hae : ∀ᵐ ω ∂hpath P ν, L.indicator (1 : (ℕ → E) → ℝ) ω = c.toReal := by
    filter_upwards [hlev, ae_all_iff.mpr hce] with ω h1 h2
    have : (fun n => ((hpath P ν)[L.indicator (1 : (ℕ → E) → ℝ) | Filtration.piLE n]) ω) =
        fun _ => c.toReal := funext h2
    rw [this] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  obtain ⟨ω, hω⟩ := hae.exists
  by_cases hωL : ω ∈ L
  · right
    rw [Set.indicator_of_mem hωL, Pi.one_apply] at hω
    exact (ENNReal.toReal_eq_one_iff c).mp hω.symm
  · left
    rw [Set.indicator_of_notMem hωL] at hω
    rcases (ENNReal.toReal_eq_zero_iff c).mp hω.symm with h | h
    · exact h
    · exact absurd h hcT

/-- **Harris lift**: a bounded harmonic function of a chain `Q = A ∘ B` (on `Z`) whose
"projected" chain `R = B ∘ A` (on `X`) is Harris recurrent is constant. -/
theorem harm_lift {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (R : Kernel X X) [IsMarkovKernel R] (hH : RiskSensMDP.AverageCost.IsHarrisRecurrent R)
    (A : Kernel X Z) [IsMarkovKernel A] (B : Kernel Z X) [IsMarkovKernel B] (Q : Kernel Z Z)
    (hQ : ∀ z (f : Z → ℝ≥0∞), Measurable f → ∫⁻ w, f w ∂Q z = ∫⁻ x', ∫⁻ w, f w ∂A x' ∂B z)
    (hR : ∀ x (f : X → ℝ≥0∞), Measurable f → ∫⁻ y, f y ∂(R x) = ∫⁻ z, ∫⁻ y, f y ∂(B z) ∂(A x))
    {g : Z → ℝ≥0∞} (hg : Measurable g) (hg1 : ∀ z, g z ≤ 1)
    (hharm : ∀ z, ∫⁻ w, g w ∂Q z = g z) (z w : Z) : g z = g w := by
  set k : X → ℝ≥0∞ := fun x => ∫⁻ v, g v ∂A x with hk
  have hkm : Measurable k := hg.lintegral_kernel
  have hk1 : ∀ x, k x ≤ 1 := fun x => by
    calc k x ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂A x := lintegral_mono fun v => hg1 v
      _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
  have hkT : ∀ x, k x ≠ ⊤ := fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (hk1 x)
  have hkharm : ∀ x, ∫⁻ y, k y ∂(R x) = k x := by
    intro x
    rw [hR x k hkm]
    refine lintegral_congr fun v => ?_
    rw [← hQ v g hg, hharm]
  have hconst : ∀ x y, k x = k y := by
    intro x y
    have := harm_const R hH (h := fun x => (k x).toReal) hkm.ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg) (B := 1)
      (fun x => ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hk1 x))
      (fun x => by simp only [ENNReal.ofReal_toReal (hkT _)]; exact hkharm x) x y
    exact (ENNReal.toReal_eq_toReal_iff' (hkT x) (hkT y)).mp this
  have hne : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    have h1 := measure_univ (μ := B z)
    rw [Set.univ_eq_empty_iff.mpr hX, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨x0⟩ := hne
  have hg_eq : ∀ v, g v = k x0 := by
    intro v
    rw [← hharm v, hQ v g hg]
    calc ∫⁻ x', ∫⁻ w, g w ∂A x' ∂B v = ∫⁻ _, k x0 ∂B v := lintegral_congr fun x' => hconst x' x0
      _ = k x0 := by rw [lintegral_const, measure_univ, mul_one]
  rw [hg_eq z, hg_eq w]

end FiniteMemQL.Convergence.AppAAux
set_option autoImplicit false
set_option linter.all false

namespace Birkhoff1931Aux

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

/-- Running maximum `max (S_0 g, ..., S_N g)` of Birkhoff sums (with `S_0 g = 0`). -/
noncomputable def runMax (T : X → X) (g : X → ℝ) : ℕ → X → ℝ
  | 0, _ => 0
  | N + 1, x => max (runMax T g N x) (birkhoffSum T g (N + 1) x)

lemma runMax_zero (T : X → X) (g : X → ℝ) (x : X) : runMax T g 0 x = 0 := rfl

lemma runMax_succ (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) :
    runMax T g (N + 1) x = max (runMax T g N x) (birkhoffSum T g (N + 1) x) := rfl

lemma runMax_nonneg (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) : 0 ≤ runMax T g N x := by
  induction N with
  | zero => rw [runMax_zero]
  | succ N ih => rw [runMax_succ]; exact le_trans ih (le_max_left _ _)

lemma le_runMax (T : X → X) (g : X → ℝ) {N k : ℕ} (hk : k ≤ N) (x : X) :
    birkhoffSum T g k x ≤ runMax T g N x := by
  induction N with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    rw [runMax_zero, birkhoffSum_zero]
  | succ N ih =>
    rw [runMax_succ]
    rcases Nat.lt_or_ge k (N + 1) with h | h
    · exact le_trans (ih (by omega)) (le_max_left _ _)
    · have hk' : k = N + 1 := by omega
      subst hk'
      exact le_max_right _ _

lemma runMax_eq (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) :
    ∃ k ≤ N, runMax T g N x = birkhoffSum T g k x := by
  induction N with
  | zero => exact ⟨0, le_refl _, by rw [runMax_zero, birkhoffSum_zero]⟩
  | succ N ih =>
    obtain ⟨k, hk, he⟩ := ih
    rw [runMax_succ]
    rcases le_total (runMax T g N x) (birkhoffSum T g (N + 1) x) with h | h
    · exact ⟨N + 1, le_refl _, max_eq_right h⟩
    · exact ⟨k, by omega, by rw [max_eq_left h, he]⟩

lemma runMax_le (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) (hpos : 0 < runMax T g N x) :
    runMax T g N x ≤ g x + runMax T g N (T x) := by
  obtain ⟨k, hk, he⟩ := runMax_eq T g N x
  rcases k with _ | j
  · rw [he, birkhoffSum_zero] at hpos
    exact absurd hpos (lt_irrefl 0)
  · rw [he, birkhoffSum_succ']
    have := le_runMax T g (show j ≤ N by omega) (T x)
    linarith

lemma measurable_birkhoffSum' {T : X → X} {g : X → ℝ} (hT : Measurable T) (hg : Measurable g)
    (n : ℕ) : Measurable (birkhoffSum T g n) := by
  have e : birkhoffSum T g n = fun x => ∑ k ∈ Finset.range n, g (T^[k] x) := rfl
  rw [e]
  exact Finset.measurable_sum _ (fun k _ => hg.comp (hT.iterate k))

lemma integrable_birkhoffSum' {μ : Measure X} {T : X → X} {g : X → ℝ}
    (hT : MeasurePreserving T μ μ) (hg : Integrable g μ) (n : ℕ) :
    Integrable (birkhoffSum T g n) μ := by
  have e : birkhoffSum T g n = fun x => ∑ k ∈ Finset.range n, g (T^[k] x) := rfl
  rw [e]
  exact integrable_finset_sum _ (fun k _ => (hT.iterate k).integrable_comp_of_integrable hg)

lemma measurable_runMax {T : X → X} {g : X → ℝ} (hT : Measurable T) (hg : Measurable g)
    (N : ℕ) : Measurable (runMax T g N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    have e : runMax T g (N + 1) = fun x => max (runMax T g N x) (birkhoffSum T g (N + 1) x) :=
      rfl
    rw [e]
    exact ih.max (measurable_birkhoffSum' hT hg (N + 1))

lemma integrable_runMax {μ : Measure X} {T : X → X} {g : X → ℝ}
    (hT : MeasurePreserving T μ μ) (hgm : Measurable g) (hg : Integrable g μ) (N : ℕ) :
    Integrable (runMax T g N) μ := by
  induction N with
  | zero =>
    have e : runMax T g 0 = fun _ => (0 : ℝ) := rfl
    rw [e]
    exact integrable_zero _ _ _
  | succ N ih =>
    have hS := integrable_birkhoffSum' hT hg (N + 1)
    refine Integrable.mono' (ih.abs.add hS.abs)
      (measurable_runMax hT.measurable hgm (N + 1)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, runMax_succ, abs_le]
    have a1 := le_abs_self (runMax T g N x)
    have a2 := neg_abs_le (runMax T g N x)
    have b1 := le_abs_self (birkhoffSum T g (N + 1) x)
    have b2 := neg_abs_le (birkhoffSum T g (N + 1) x)
    have a0 := abs_nonneg (runMax T g N x)
    have b0 := abs_nonneg (birkhoffSum T g (N + 1) x)
    constructor
    · exact le_max_of_le_left (by linarith)
    · exact max_le (by linarith) (by linarith)

/-- **Maximal ergodic theorem** (Garsia's proof). -/
theorem maximal_ergodic (μ : Measure X) [IsFiniteMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hgm : Measurable g) (hg : Integrable g μ) :
    0 ≤ ∫ x in {x | ∃ n, 0 < birkhoffSum T g n x}, g x ∂μ := by
  let F : ℕ → Set X := fun N => {x | 0 < runMax T g N x}
  have hFm : ∀ N, MeasurableSet (F N) := fun N =>
    measurableSet_lt measurable_const (measurable_runMax hT.measurable hgm N)
  have hmono : Monotone F := by
    apply monotone_nat_of_le_succ
    intro N x hx
    show 0 < runMax T g (N + 1) x
    rw [runMax_succ]
    exact lt_max_of_lt_left hx
  have hU : (⋃ N, F N) = {x | ∃ n, 0 < birkhoffSum T g n x} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, F]
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨k, -, he⟩ := runMax_eq T g N x
      exact ⟨k, he ▸ hN⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, lt_of_lt_of_le hn (le_runMax T g le_rfl x)⟩
  have hNonneg : ∀ N, 0 ≤ ∫ x in F N, g x ∂μ := by
    intro N
    have hMm := measurable_runMax hT.measurable hgm N
    have hMi := integrable_runMax hT hgm hg N
    have hMTi : Integrable (fun x => runMax T g N (T x)) μ :=
      hT.integrable_comp_of_integrable hMi
    have h1 : ∫ x in F N, (runMax T g N x - runMax T g N (T x)) ∂μ ≤ ∫ x in F N, g x ∂μ := by
      apply setIntegral_mono_on (hMi.sub hMTi).integrableOn hg.integrableOn (hFm N)
      intro x hx
      have := runMax_le T g N x hx
      show runMax T g N x - runMax T g N (T x) ≤ g x
      linarith
    have h2 : ∫ x in F N, (runMax T g N x - runMax T g N (T x)) ∂μ
        = ∫ x in F N, runMax T g N x ∂μ - ∫ x in F N, runMax T g N (T x) ∂μ :=
      integral_sub hMi.integrableOn hMTi.integrableOn
    have h3 : ∫ x in F N, runMax T g N x ∂μ = ∫ x, runMax T g N x ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hx' : ¬ (0 < runMax T g N x) := hx
      exact le_antisymm (not_lt.1 hx') (runMax_nonneg T g N x)
    have h4 : ∫ x in F N, runMax T g N (T x) ∂μ ≤ ∫ x, runMax T g N (T x) ∂μ :=
      setIntegral_le_integral hMTi (Eventually.of_forall fun x => runMax_nonneg T g N (T x))
    have h5 : ∫ x, runMax T g N (T x) ∂μ = ∫ x, runMax T g N x ∂μ := by
      have hfm : AEStronglyMeasurable (runMax T g N) (Measure.map T μ) := by
        rw [hT.map_eq]; exact hMm.aestronglyMeasurable
      have := integral_map hT.measurable.aemeasurable hfm
      rw [hT.map_eq] at this
      exact this.symm
    linarith
  have ht := tendsto_setIntegral_of_monotone hFm hmono (hg.integrableOn)
  rw [hU] at ht
  exact ge_of_tendsto' ht hNonneg

lemma iterate_mem_iff {T : X → X} {D : Set X} (hD : T ⁻¹' D = D) (k : ℕ) (x : X) :
    T^[k] x ∈ D ↔ x ∈ D := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change T^[k] x ∈ T ⁻¹' D ↔ _
    rw [hD, ih]

lemma birkhoffSum_indicator {T : X → X} {D : Set X} (hD : T ⁻¹' D = D) (h : X → ℝ) (n : ℕ)
    (x : X) : birkhoffSum T (D.indicator h) n x = D.indicator (birkhoffSum T h n) x := by
  by_cases hx : x ∈ D
  · rw [Set.indicator_of_mem hx]
    simp only [birkhoffSum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Set.indicator_of_mem ((iterate_mem_iff hD k x).2 hx)]
  · rw [Set.indicator_of_notMem hx]
    simp only [birkhoffSum]
    apply Finset.sum_eq_zero
    intro k _
    rw [Set.indicator_of_notMem (mt (iterate_mem_iff hD k x).1 hx)]

/-- Points where the Birkhoff sums of `h` are unbounded above. -/
def unbSet (T : X → X) (h : X → ℝ) : Set X :=
  {x | ∀ M : ℕ, ∃ n, (M : ℝ) < birkhoffSum T h n x}

lemma mem_unbSet (T : X → X) (h : X → ℝ) (x : X) :
    x ∈ unbSet T h ↔ ∀ M : ℕ, ∃ n, (M : ℝ) < birkhoffSum T h n x := Iff.rfl

lemma unbSet_invariant (T : X → X) (h : X → ℝ) : T ⁻¹' unbSet T h = unbSet T h := by
  ext x
  rw [Set.mem_preimage, mem_unbSet, mem_unbSet]
  constructor
  · intro H M
    obtain ⟨M', hM'⟩ := exists_nat_gt ((M : ℝ) - h x)
    obtain ⟨n, hn⟩ := H M'
    refine ⟨n + 1, ?_⟩
    rw [birkhoffSum_succ']
    linarith
  · intro H M
    obtain ⟨M', hM'⟩ := exists_nat_gt ((M : ℝ) + |h x|)
    obtain ⟨n', hn'⟩ := H M'
    rcases n' with _ | n
    · rw [birkhoffSum_zero] at hn'
      exact absurd hn' (not_lt.2 (Nat.cast_nonneg _))
    · refine ⟨n, ?_⟩
      rw [birkhoffSum_succ'] at hn'
      linarith [le_abs_self (h x)]

lemma measurableSet_unbSet {T : X → X} {h : X → ℝ} (hT : Measurable T) (hh : Measurable h) :
    MeasurableSet (unbSet T h) := by
  have e : unbSet T h = ⋂ M : ℕ, ⋃ n : ℕ, {x | (M : ℝ) < birkhoffSum T h n x} := by
    ext x; simp [unbSet]
  rw [e]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (measurable_birkhoffSum' hT hh n)

lemma upper_bound (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hgm : Measurable g) (hg : Integrable g μ)
    (hzero : ∀ s, MeasurableSet[MeasurableSpace.invariants T] s → ∫ x in s, g x ∂μ = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂μ, ∃ M : ℕ, ∀ n : ℕ, birkhoffSum T g n x - n * ε ≤ M := by
  let h : X → ℝ := fun x => g x - ε
  have hhm : Measurable h := hgm.sub measurable_const
  have hhi : Integrable h μ := hg.sub (integrable_const ε)
  have hDm : MeasurableSet (unbSet T h) := measurableSet_unbSet hT.measurable hhm
  have hDinv := unbSet_invariant T h
  have hDI : MeasurableSet[MeasurableSpace.invariants T] (unbSet T h) := ⟨hDm, hDinv⟩
  have hmax := maximal_ergodic μ hT (hhm.indicator hDm) (hhi.indicator hDm)
  have hset : {x | ∃ n, 0 < birkhoffSum T ((unbSet T h).indicator h) n x} = unbSet T h := by
    ext x
    constructor
    · rintro ⟨n, hn⟩
      rw [birkhoffSum_indicator hDinv] at hn
      by_contra hx
      rw [Set.indicator_of_notMem hx] at hn
      exact lt_irrefl _ hn
    · intro hx
      obtain ⟨n, hn⟩ := (mem_unbSet T h x).1 hx 0
      refine ⟨n, ?_⟩
      rw [birkhoffSum_indicator hDinv, Set.indicator_of_mem hx]
      exact_mod_cast hn
  rw [hset, setIntegral_indicator hDm, Set.inter_self] at hmax
  have e2 : ∫ x in unbSet T h, h x ∂μ = ∫ x in unbSet T h, g x ∂μ - μ.real (unbSet T h) * ε := by
    rw [integral_sub hg.integrableOn (integrable_const ε).integrableOn, setIntegral_const,
      smul_eq_mul]
  rw [e2, hzero _ hDI] at hmax
  have hr : μ.real (unbSet T h) = 0 := by
    have h0 : 0 ≤ μ.real (unbSet T h) := measureReal_nonneg
    have h1 : μ.real (unbSet T h) * ε ≤ 0 := by linarith
    by_contra hne
    have : 0 < μ.real (unbSet T h) * ε := mul_pos (lt_of_le_of_ne h0 (Ne.symm hne)) hε
    linarith
  have hμD : μ (unbSet T h) = 0 := (measureReal_eq_zero_iff (measure_ne_top μ _)).1 hr
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμD] with x hx
  rw [mem_unbSet] at hx
  push Not at hx
  obtain ⟨M, hM⟩ := hx
  refine ⟨M, fun n => ?_⟩
  have h1 := hM n
  have hs : birkhoffSum T h n x = birkhoffSum T g n x - n * ε := by
    simp [h, birkhoffSum, Finset.sum_sub_distrib]
  linarith

lemma eventually_le_of_bound {T : X → X} {g : X → ℝ} {x : X} {ε : ℝ} (hε : 0 < ε)
    (hb : ∃ M : ℕ, ∀ n : ℕ, birkhoffSum T g n x - n * ε ≤ M) :
    ∀ᶠ n in atTop, birkhoffAverage ℝ T g n x ≤ 2 * ε := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨N, hN⟩ := exists_nat_gt ((M : ℝ) / ε)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnN : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have h1 : (M : ℝ) < N * ε := by rwa [div_lt_iff₀ hε] at hN
  have h2 : (N : ℝ) * ε ≤ n * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
  have h3 := hM n
  show (n : ℝ)⁻¹ • birkhoffSum T g n x ≤ 2 * ε
  rw [smul_eq_mul, inv_mul_le_iff₀ hnpos]
  linarith

lemma tendsto_zero (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hgm : Measurable g) (hg : Integrable g μ)
    (hzero : ∀ s, MeasurableSet[MeasurableSpace.invariants T] s → ∫ x in s, g x ∂μ = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T g n x) atTop (𝓝 0) := by
  have hzero' : ∀ s, MeasurableSet[MeasurableSpace.invariants T] s →
      ∫ x in s, (-g) x ∂μ = 0 := by
    intro s hs
    simp only [Pi.neg_apply]
    rw [integral_neg, hzero s hs, neg_zero]
  have hup : ∀ k : ℕ, ∀ᵐ x ∂μ, ∃ M : ℕ, ∀ n : ℕ,
      birkhoffSum T g n x - n * (1 / ((k : ℝ) + 1)) ≤ M :=
    fun k => upper_bound μ hT hgm hg hzero _ (by positivity)
  have hlo : ∀ k : ℕ, ∀ᵐ x ∂μ, ∃ M : ℕ, ∀ n : ℕ,
      birkhoffSum T (-g) n x - n * (1 / ((k : ℝ) + 1)) ≤ M :=
    fun k => upper_bound μ hT hgm.neg hg.neg hzero' _ (by positivity)
  rw [← ae_all_iff] at hup hlo
  filter_upwards [hup, hlo] with x hu hl
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < -a / 2 by linarith)
    filter_upwards [eventually_le_of_bound (by positivity) (hl k)] with n hn
    have hneg : birkhoffAverage ℝ T (-g) n x = -birkhoffAverage ℝ T g n x := by
      rw [birkhoffAverage_neg, Pi.neg_apply, Pi.neg_apply]
    rw [hneg] at hn
    linarith
  · intro b hb
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < b / 2 by linarith)
    filter_upwards [eventually_le_of_bound (by positivity) (hu k)] with n hn
    linarith

end Birkhoff1931Aux

open MeasureTheory Filter Topology in
theorem birkhoff_ae_top {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (T : X → X) (hT : MeasurePreserving T μ μ) (f : X → ℝ)
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n x) atTop
      (𝓝 (condExp (MeasurableSpace.invariants T) μ f x)) := by
  have hf'm : StronglyMeasurable (hf.1.mk f) := hf.1.stronglyMeasurable_mk
  have hff' : f =ᵐ[μ] hf.1.mk f := hf.1.ae_eq_mk
  have hf'i : Integrable (hf.1.mk f) μ := hf.congr hff'
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace X› := MeasurableSpace.invariants_le T
  have hcm : StronglyMeasurable[MeasurableSpace.invariants T]
      (condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) := stronglyMeasurable_condExp
  have hcinv : condExp (MeasurableSpace.invariants T) μ (hf.1.mk f) ∘ T
      = condExp (MeasurableSpace.invariants T) μ (hf.1.mk f) :=
    MeasurableSpace.comp_eq_of_measurable_invariants hcm.measurable
  have hcM : Measurable (condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) :=
    (hcm.mono hm).measurable
  have hci : Integrable (condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) μ :=
    integrable_condExp
  have hgm : Measurable (hf.1.mk f - condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) :=
    hf'm.measurable.sub hcM
  have hgi : Integrable (hf.1.mk f - condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) μ :=
    hf'i.sub hci
  have hzero : ∀ s, MeasurableSet[MeasurableSpace.invariants T] s →
      ∫ x in s, (hf.1.mk f - condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) x ∂μ = 0 := by
    intro s hs
    simp only [Pi.sub_apply]
    rw [integral_sub hf'i.integrableOn hci.integrableOn, setIntegral_condExp hm hf'i hs, sub_self]
  have key := Birkhoff1931Aux.tendsto_zero μ hT hgm hgi hzero
  have hcc : condExp (MeasurableSpace.invariants T) μ f
      =ᵐ[μ] condExp (MeasurableSpace.invariants T) μ (hf.1.mk f) := condExp_congr_ae hff'
  have hA : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffAverage ℝ T f n x = birkhoffAverage ℝ T (hf.1.mk f) n x := by
    rw [ae_all_iff]
    intro n
    exact hT.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hff' n
  filter_upwards [key, hcc, hA] with x hx hcx hAx
  rw [hcx]
  have hev : ∀ᶠ n in atTop,
      birkhoffAverage ℝ T (hf.1.mk f - condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) n x
        + condExp (MeasurableSpace.invariants T) μ (hf.1.mk f) x
        = birkhoffAverage ℝ T f n x := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [hAx n, birkhoffAverage_sub, Pi.sub_apply, Pi.sub_apply,
      birkhoffAverage_of_comp_eq ℝ hcinv hn']
    ring
  have ht := hx.add (tendsto_const_nhds (x := condExp (MeasurableSpace.invariants T) μ (hf.1.mk f) x))
  rw [zero_add] at ht
  exact ht.congr' hev
namespace FiniteMemQL.Convergence.AppAAux

open FiniteMemQL.Convergence

section Glue

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

lemma pathMeasure_eq_hpath (M : POMDP X Y U) (μ : Measure X) (σ : Measure U)
    [IsProbabilityMeasure σ] :
    pathMeasure M μ σ = hpath (stepKernel M σ) (initLaw M μ σ) := rfl

/-- `kA x` = law of `(x, Y, U)` with `Y ~ O(·|x)` and an independent `U ~ σ`. -/
noncomputable def kA (M : POMDP X Y U) (σ : Measure U) : Kernel X (X × Y × U) :=
  Kernel.map ((Kernel.id ×ₖ M.O) ×ₖ Kernel.const X σ)
    (fun q : (X × Y) × U => (q.1.1, q.1.2, q.2))

scoped instance kA_markov (M : POMDP X Y U) (σ : Measure U) [IsProbabilityMeasure σ] :
    IsMarkovKernel (kA M σ) := by
  unfold kA; exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- `kB (x, y, u) = T(· | x, u)`. -/
noncomputable def kB (M : POMDP X Y U) : Kernel (X × Y × U) X :=
  M.T.comap (fun p : X × Y × U => (p.1, p.2.2)) (by fun_prop)

scoped instance kB_markov (M : POMDP X Y U) : IsMarkovKernel (kB M) := by
  unfold kB; exact Kernel.IsMarkovKernel.comap _ _

lemma lintegral_kA (M : POMDP X Y U) (σ : Measure U) [IsProbabilityMeasure σ] (x : X)
    {f : X × Y × U → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ w, f w ∂kA M σ x = ∫⁻ y, ∫⁻ u, f (x, y, u) ∂σ ∂M.O x := by
  have hg : Measurable (fun q : (X × Y) × U => (q.1.1, q.1.2, q.2)) := by fun_prop
  have hF : Measurable (fun q : (X × Y) × U => f (q.1.1, q.1.2, q.2)) := hf.comp hg
  unfold kA
  rw [Kernel.lintegral_map _ hg _ hf, Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, lintegral_prod _ hF.aemeasurable, lintegral_prod, lintegral_dirac']
  all_goals first
    | rfl
    | exact hF.lintegral_prod_right'.aemeasurable
    | exact hF.lintegral_prod_right'.lintegral_prod_right'
    | exact hF.lintegral_prod_right'
    | exact hF

lemma lintegral_step (M : POMDP X Y U) (σ : Measure U) [IsProbabilityMeasure σ]
    (z : X × Y × U) {f : X × Y × U → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ w, f w ∂stepKernel M σ z = ∫⁻ x', ∫⁻ w, f w ∂kA M σ x' ∂kB M z := by
  have hg : Measurable (fun q : (X × Y) × U => (q.1.1, q.1.2, q.2)) := by fun_prop
  have hF : Measurable (fun q : (X × Y) × U => f (q.1.1, q.1.2, q.2)) := hf.comp hg
  unfold stepKernel
  rw [Kernel.lintegral_map _ hg _ hf, Kernel.prod_apply, Kernel.const_apply,
    lintegral_prod _ hF.aemeasurable, Kernel.lintegral_compProd]
  · unfold kB
    rw [Kernel.comap_apply]
    refine lintegral_congr fun x' => ?_
    rw [lintegral_kA M σ x' hf, Kernel.comap_apply]
  all_goals first
    | rfl
    | exact hF.lintegral_prod_right'.aemeasurable
    | exact hF.lintegral_prod_right'.lintegral_prod_right'
    | exact hF.lintegral_prod_right'
    | exact hF

lemma lintegral_expl (M : POMDP X Y U) (σ : Measure U) [IsProbabilityMeasure σ] (x : X)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂explKernel M σ x = ∫⁻ z, ∫⁻ y, f y ∂kB M z ∂kA M σ x := by
  have hT : Measurable (fun p : X × U => ∫⁻ y, f y ∂M.T p) := hf.lintegral_kernel
  have hB : Measurable (fun z : X × Y × U => ∫⁻ y, f y ∂kB M z) := hf.lintegral_kernel
  unfold explKernel
  rw [Kernel.lintegral_comp _ _ _ hf, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    lintegral_prod _ hT.aemeasurable, lintegral_dirac' _ hT.lintegral_prod_right',
    lintegral_kA M σ x hB]
  simp only [kB, Kernel.comap_apply]
  rw [lintegral_const, measure_univ, mul_one]

lemma lintegral_initLaw_kA (M : POMDP X Y U) (μ : Measure X) [IsProbabilityMeasure μ]
    (σ : Measure U) [IsProbabilityMeasure σ] {f : X × Y × U → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ w, f w ∂initLaw M μ σ = ∫⁻ x, ∫⁻ w, f w ∂kA M σ x ∂μ := by
  have hg : Measurable (fun q : (X × Y) × U => (q.1.1, q.1.2, q.2)) := by fun_prop
  have hF : Measurable (fun q : (X × Y) × U => f (q.1.1, q.1.2, q.2)) := hf.comp hg
  unfold initLaw
  rw [lintegral_map hf hg, lintegral_prod _ hF.aemeasurable, Measure.lintegral_compProd]
  · refine lintegral_congr fun x => ?_
    rw [lintegral_kA M σ x hf]
  all_goals first
    | rfl
    | exact hF.lintegral_prod_right'.aemeasurable
    | exact hF.lintegral_prod_right'.lintegral_prod_right'
    | exact hF.lintegral_prod_right'
    | exact hF

scoped instance initLaw_prob (M : POMDP X Y U) (μ : Measure X) [IsProbabilityMeasure μ]
    (σ : Measure U) [IsProbabilityMeasure σ] : IsProbabilityMeasure (initLaw M μ σ) := by
  unfold initLaw; exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The stationary initial law is invariant for the exploration step kernel. -/
lemma initLaw_bind (M : POMDP X Y U) (σ : Measure U) [IsProbabilityMeasure σ]
    (πs : Measure X) [IsProbabilityMeasure πs] (hπs : Kernel.Invariant (explKernel M σ) πs) :
    (initLaw M πs σ).bind (stepKernel M σ) = initLaw M πs σ := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have h1 : Measurable fun x => ∫⁻ w, f w ∂kA M σ x := hf.lintegral_kernel
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,
    lintegral_initLaw_kA M πs σ hf.lintegral_kernel, lintegral_initLaw_kA M πs σ hf]
  have : ∀ x, ∫⁻ z, ∫⁻ w, f w ∂stepKernel M σ z ∂kA M σ x =
      ∫⁻ y, ∫⁻ w, f w ∂kA M σ y ∂explKernel M σ x := by
    intro x
    rw [lintegral_expl M σ x h1]
    exact lintegral_congr fun z => lintegral_step M σ z hf
  simp_rw [this]
  conv_rhs => rw [← hπs]
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) h1.aemeasurable]

end Glue

section Shift

variable {E : Type*} [MeasurableSpace E]

lemma lintegral_hpath_shift_one (P : Kernel E E) [IsMarkovKernel P] (ν : Measure E)
    [IsProbabilityMeasure ν] {f : (ℕ → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (fun t => ω (1 + t)) ∂hpath P ν = ∫⁻ ω, f ω ∂hpath P (ν.bind P) := by
  have hΨ : Measurable fun z : E => ∫⁻ ω, f ω ∂hpath P (Measure.dirac z) :=
    measurable_lintegral_hpath_dirac P hf
  haveI : IsProbabilityMeasure (ν.bind P) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    simp
  rw [lintegral_hpath_bind P (ν.bind P) hf,
    Measure.lintegral_bind (Kernel.aemeasurable _) hΨ.aemeasurable,
    lintegral_hpath_shift_full P ν 1 (F := fun p => f p.2) (hf.comp measurable_snd)]
  have h2 := lintegral_hpath_markov P ν 0 (Φ := fun _ z => ∫⁻ ω, f ω ∂hpath P (Measure.dirac z))
    (hΨ.comp measurable_snd)
  rw [show (fun ω : ℕ → E => ∫⁻ ω', f ω' ∂hpath P (Measure.dirac (ω 1))) =
    fun ω => ∫⁻ ω', f ω' ∂hpath P (Measure.dirac (ω (0 + 1))) from rfl, h2,
    lintegral_hpath_zero P ν (F := fun y => ∫⁻ z, ∫⁻ ω, f ω ∂hpath P (Measure.dirac z) ∂P y)
      hΨ.lintegral_kernel]

lemma shift_iterate (k : ℕ) (ω : ℕ → E) :
    (fun ω : ℕ → E => fun t => ω (1 + t))^[k] ω = fun t => ω (k + t) := by
  induction k generalizing ω with
  | zero => funext t; rw [Function.iterate_zero_apply, Nat.zero_add]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    funext t; congr 1; omega

lemma measurable_shift_k (k : ℕ) : Measurable fun ω : ℕ → E => fun t => ω (k + t) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

end Shift

section Glue2

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

lemma shift_mp (M : POMDP X Y U) (σ : Measure U) [IsProbabilityMeasure σ]
    (πs : Measure X) [IsProbabilityMeasure πs] (hπs : Kernel.Invariant (explKernel M σ) πs) :
    MeasurePreserving (fun ω : ℕ → X × Y × U => fun t => ω (1 + t))
      (pathMeasure M πs σ) (pathMeasure M πs σ) := by
  refine ⟨measurable_shift_k 1, Measure.ext_of_lintegral _ fun f hf => ?_⟩
  rw [lintegral_map hf (measurable_shift_k 1), pathMeasure_eq_hpath,
    lintegral_hpath_shift_one _ _ hf, initLaw_bind M σ πs hπs]

/-- **0-1 law** for shift-invariant path events under Harris recurrence: the probability does not
depend on the initial law and is `0` or `1`. -/
theorem inv_const [Nonempty X] [Nonempty Y] [Nonempty U] (M : POMDP X Y U) (σ : Measure U)
    [IsProbabilityMeasure σ] (hH : RiskSensMDP.AverageCost.IsHarrisRecurrent (explKernel M σ))
    {L : Set (ℕ → X × Y × U)} (hL : MeasurableSet L)
    (hinv : ∀ ω : ℕ → X × Y × U, (fun t => ω (1 + t)) ∈ L ↔ ω ∈ L) :
    ∃ c : ℝ≥0∞, (c = 0 ∨ c = 1) ∧
      ∀ (μ : Measure X) [IsProbabilityMeasure μ], pathMeasure M μ σ L = c := by
  have hgm : Measurable fun z : X × Y × U => hpath (stepKernel M σ) (Measure.dirac z) L :=
    measurable_hpath_dirac _ hL
  have hconst : ∀ z w : X × Y × U, hpath (stepKernel M σ) (Measure.dirac z) L =
      hpath (stepKernel M σ) (Measure.dirac w) L :=
    harm_lift (explKernel M σ) hH (kA M σ) (kB M) (stepKernel M σ)
      (fun z f hf => lintegral_step M σ z hf) (fun x f hf => lintegral_expl M σ x hf) hgm
      (fun z => prob_le_one) (harm_of_shift_invariant _ hL hinv)
  let z0 : X × Y × U := Classical.arbitrary _
  refine ⟨hpath (stepKernel M σ) (Measure.dirac z0) L,
    invariant_zero_one _ (Measure.dirac z0) hL hinv (fun z => hconst z z0), ?_⟩
  intro μ _
  rw [pathMeasure_eq_hpath, ← lintegral_indicator_one hL,
    lintegral_hpath_bind _ _ (F := L.indicator (1 : (ℕ → X × Y × U) → ℝ≥0∞))
      (measurable_one.indicator hL)]
  simp_rw [lintegral_indicator_one hL]
  rw [show (fun z => hpath (stepKernel M σ) (Measure.dirac z) L) =
      fun _ => hpath (stepKernel M σ) (Measure.dirac z0) L from funext fun z => hconst z z0,
    lintegral_const, measure_univ, mul_one]

/-- **C3b**: a path event of stationary probability zero occurs only finitely often. -/
theorem C3b [Nonempty X] [Nonempty Y] [Nonempty U] (M : POMDP X Y U) (σ : Measure U)
    [IsProbabilityMeasure σ] (hH : RiskSensMDP.AverageCost.IsHarrisRecurrent (explKernel M σ))
    (πs : Measure X) [IsProbabilityMeasure πs] (hπs : Kernel.Invariant (explKernel M σ) πs)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (A : Set (ℕ → X × Y × U)) (hA : MeasurableSet A) (h0 : pathMeasure M πs σ A = 0) :
    ∀ᵐ ω ∂pathMeasure M μ σ, ∀ᶠ k in atTop, (fun t => ω (k + t)) ∉ A := by
  let L : Set (ℕ → X × Y × U) := {ω | ∃ᶠ k in atTop, (fun t => ω (k + t)) ∈ A}
  have hLeq : L = ⋂ a : ℕ, ⋃ b : ℕ, ⋃ (_ : a ≤ b),
      (fun ω : ℕ → X × Y × U => fun t => ω (b + t)) ⁻¹' A := by
    ext ω; simp [L, Filter.frequently_atTop]
  have hLm : MeasurableSet L := by
    rw [hLeq]
    exact MeasurableSet.iInter fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun _ => measurable_shift_k b hA
  have hinv : ∀ ω : ℕ → X × Y × U, (fun t => ω (1 + t)) ∈ L ↔ ω ∈ L := by
    intro ω
    simp only [L, Set.mem_setOf_eq, Filter.frequently_atTop]
    constructor
    · intro h a
      obtain ⟨b, hb, hbA⟩ := h a
      refine ⟨1 + b, by omega, ?_⟩
      convert hbA using 1
      funext t; congr 1; omega
    · intro h a
      obtain ⟨b, hb, hbA⟩ := h (a + 1)
      refine ⟨b - 1, by omega, ?_⟩
      convert hbA using 1
      funext t; congr 1; omega
  obtain ⟨c, -, hc⟩ := inv_const M σ hH hLm hinv
  have hstat : pathMeasure M πs σ L = 0 := by
    have hmp := shift_mp M σ πs hπs
    refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null fun b => ?_ :
      pathMeasure M πs σ (⋃ b : ℕ, (fun ω : ℕ → X × Y × U => fun t => ω (b + t)) ⁻¹' A) = 0)
    · rw [hLeq] at hω
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hω 0)
      exact Set.mem_iUnion.mpr ⟨b, (Set.mem_iUnion.mp hb).2⟩
    · have hpre := (hmp.iterate b).measure_preimage hA.nullMeasurableSet
      have heq : (fun ω : ℕ → X × Y × U => fun t => ω (1 + t))^[b] ⁻¹' A =
          (fun ω : ℕ → X × Y × U => fun t => ω (b + t)) ⁻¹' A := by
        ext ω; simp only [Set.mem_preimage, shift_iterate]
      rw [← heq, hpre, h0]
  have hμ : pathMeasure M μ σ L = 0 := by rw [hc μ, ← hc πs, hstat]
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hμ
  simp only [Set.mem_setOf_eq, Filter.not_eventually, not_not] at hω
  exact hω

end Glue2

end FiniteMemQL.Convergence.AppAAux
namespace FiniteMemQL.Convergence.AppAAux

open FiniteMemQL.Convergence

section C3a

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

/-- The one-step path shift. -/
abbrev sh1 {Z : Type*} : (ℕ → Z) → (ℕ → Z) := fun ω t => ω (1 + t)

lemma birkhoffAverage_sh1 (G : (ℕ → X × Y × U) → ℝ) (n : ℕ) (ω : ℕ → X × Y × U) :
    birkhoffAverage ℝ sh1 G n ω = (n : ℝ)⁻¹ * ∑ k ∈ range n, G (fun t => ω (k + t)) := by
  simp only [birkhoffAverage, birkhoffSum, sh1, shift_iterate, smul_eq_mul]

lemma tendsto_birkhoff_sh1_iff (G : (ℕ → X × Y × U) → ℝ) {B : ℝ} (hB : ∀ ω, |G ω| ≤ B)
    (m : ℝ) (ω : ℕ → X × Y × U) :
    Tendsto (fun n => birkhoffAverage ℝ sh1 G n (sh1 ω)) atTop (𝓝 m) ↔
      Tendsto (fun n => birkhoffAverage ℝ sh1 G n ω) atTop (𝓝 m) := by
  have hd : Tendsto (fun n : ℕ => birkhoffAverage ℝ sh1 G n (sh1 ω) -
      birkhoffAverage ℝ sh1 G n ω) atTop (𝓝 0) := by
    simp_rw [birkhoffAverage_apply_sub_birkhoffAverage]
    have h0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (2 * B)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).mul_const (2 * B)
    refine squeeze_zero_norm (fun n => ?_) h0
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
    have h1 := hB (sh1^[n] ω)
    have h2 := hB ω
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  constructor
  · intro h
    simpa using h.sub hd
  · intro h
    simpa using h.add hd

/-- **C3a** (ergodic LLN along paths, Meyn–Tweedie Thm 17.1.7): from any initial law, Cesàro
averages of a bounded measurable path functional converge to its stationary mean. -/
theorem C3a [Nonempty X] [Nonempty Y] [Nonempty U] (M : POMDP X Y U) (σ : Measure U)
    [IsProbabilityMeasure σ] (hH : RiskSensMDP.AverageCost.IsHarrisRecurrent (explKernel M σ))
    (πs : Measure X) [IsProbabilityMeasure πs] (hπs : Kernel.Invariant (explKernel M σ) πs)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (G : (ℕ → X × Y × U) → ℝ) (hG : Measurable G) (hGB : ∃ B : ℝ, ∀ ω, |G ω| ≤ B) :
    ∀ᵐ ω ∂pathMeasure M μ σ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ k ∈ range n, G (fun t => ω (k + t))) atTop (𝓝 (∫ ω, G ω ∂pathMeasure M πs σ)) := by
  obtain ⟨B, hB⟩ := hGB
  haveI hPs : IsProbabilityMeasure (pathMeasure M πs σ) := by
    rw [pathMeasure_eq_hpath]; infer_instance
  haveI hPμ : IsProbabilityMeasure (pathMeasure M μ σ) := by
    rw [pathMeasure_eq_hpath]; infer_instance
  have hT : Measurable (sh1 (Z := X × Y × U)) := measurable_shift_k 1
  let L : Set (ℕ → X × Y × U) := {ω | Tendsto (fun n => birkhoffAverage ℝ sh1 G n ω) atTop
    (𝓝 (∫ ω, G ω ∂pathMeasure M πs σ))}
  have hLm : MeasurableSet L := measurableSet_tendsto _ fun n => by
    exact (Finset.measurable_sum _ fun k _ => hG.comp (hT.iterate k)).const_smul ((n : ℝ)⁻¹)
  obtain ⟨c, -, hc⟩ := inv_const M σ hH hLm (fun ω => tendsto_birkhoff_sh1_iff G hB _ ω)
  have hmp : MeasurePreserving (sh1 (Z := X × Y × U)) (pathMeasure M πs σ)
      (pathMeasure M πs σ) := shift_mp M σ πs hπs
  have herg : Ergodic (sh1 (Z := X × Y × U)) (pathMeasure M πs σ) := by
    refine ⟨hmp, ⟨fun s hs hTs => ?_⟩⟩
    have hsinv : ∀ ω : ℕ → X × Y × U, (fun t => ω (1 + t)) ∈ s ↔ ω ∈ s := fun ω =>
      show ω ∈ sh1 ⁻¹' s ↔ ω ∈ s by rw [hTs]
    obtain ⟨c', hc01, hc'⟩ := inv_const M σ hH hs hsinv
    rw [eventuallyConst_set']
    rcases hc01 with h0 | h1
    · left; rw [ae_eq_empty, hc' πs, h0]
    · right; rw [ae_eq_univ, prob_compl_eq_zero_iff hs, hc' πs, h1]
  have hGi : Integrable G (pathMeasure M πs σ) :=
    Integrable.of_bound (C := B) hG.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB ω)
  have hbk := birkhoff_ae_top (pathMeasure M πs σ) sh1 hmp G hGi
  set h := condExp (MeasurableSpace.invariants (sh1 (Z := X × Y × U))) (pathMeasure M πs σ) G
    with hh
  have hcm : StronglyMeasurable[MeasurableSpace.invariants (sh1 (Z := X × Y × U))] h :=
    stronglyMeasurable_condExp
  have hcinv : h ∘ sh1 = h := MeasurableSpace.comp_eq_of_measurable_invariants hcm.measurable
  obtain ⟨c0, hc0⟩ := herg.ae_eq_const_of_ae_eq_comp_ae
    (hcm.mono (MeasurableSpace.invariants_le _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => congrFun hcinv ω)
  have hc0m : c0 = ∫ ω, G ω ∂pathMeasure M πs σ := by
    have := integral_congr_ae hc0
    rw [hh, integral_condExp (MeasurableSpace.invariants_le _)] at this
    simpa using this.symm
  have hae : ∀ᵐ ω ∂pathMeasure M πs σ, ω ∈ L := by
    filter_upwards [hbk, hc0] with ω h1 h2
    show Tendsto _ _ _
    rw [h2, Function.const_apply, hc0m] at h1
    exact h1
  have hstat : pathMeasure M πs σ L = 1 := (prob_compl_eq_zero_iff hLm).1 (mem_ae_iff.1 hae)
  have hμL : pathMeasure M μ σ L = 1 := by rw [hc μ, ← hc πs]; exact hstat
  have hμae : ∀ᵐ ω ∂pathMeasure M μ σ, ω ∈ L :=
    mem_ae_iff.2 ((prob_compl_eq_zero_iff hLm).2 hμL)
  filter_upwards [hμae] with ω hω
  have hω' : Tendsto (fun n => birkhoffAverage ℝ sh1 G n ω) atTop
      (𝓝 (∫ ω, G ω ∂pathMeasure M πs σ)) := hω
  simpa only [birkhoffAverage_sh1] using hω'

end C3a

end FiniteMemQL.Convergence.AppAAux

namespace FiniteMemQL.Convergence.AppAAux

open FiniteMemQL.Convergence

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

/-- Forward recursion of the unnormalised posterior: newest observation last. -/
lemma unnormPost_succ (M : POMDP X Y U) (n : ℕ) (π : Measure X) (ys : Fin (n + 2) → Y)
    (us : Fin (n + 1) → U) :
    unnormPost M (n + 1) π (ys, us) =
      correct M (predict M (unnormPost M n π (Fin.init ys, Fin.init us)) (us (Fin.last n)))
        (ys (Fin.last (n + 1))) := by
  induction n generalizing π with
  | zero => rfl
  | succ n ih =>
    rw [unnormPost, ih]
    rfl

lemma lintegral_correct (M : POMDP X Y U) [MeasurableSingletonClass Y] (μ : Measure X) (y : Y)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂correct M μ y = ∫⁻ x, M.O x {y} * g x ∂μ := by
  unfold correct
  rw [lintegral_withDensity_eq_lintegral_mul _ (M.O.measurable_coe (measurableSet_singleton y)) hg]
  rfl

lemma lintegral_predict (M : POMDP X Y U) (μ : Measure X) (u : U)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂predict M μ u = ∫⁻ x, ∫⁻ x', g x' ∂M.T (x, u) ∂μ := by
  unfold predict
  exact Measure.lintegral_bind
    ((M.T.measurable).comp (measurable_id.prodMk measurable_const)).aemeasurable hg.aemeasurable

lemma lintegral_ite_eq {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [DecidableEq α] (ν : Measure α) (a0 : α) (c : ℝ≥0∞) :
    ∫⁻ a, (if a = a0 then c else 0) ∂ν = c * ν {a0} := by
  rw [← lintegral_indicator_const (measurableSet_singleton a0)]
  congr 1
  funext a
  simp [Set.indicator_apply]

lemma lintegral_initLaw (M : POMDP X Y U) (μ : Measure X) [IsProbabilityMeasure μ]
    (σ : Measure U) [IsProbabilityMeasure σ] {F : X × Y × U → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂initLaw M μ σ = ∫⁻ x, ∫⁻ y, ∫⁻ u, F (x, y, u) ∂σ ∂M.O x ∂μ := by
  have hF' : Measurable fun q : (X × Y) × U => F (q.1.1, q.1.2, q.2) := hF.comp (by fun_prop)
  unfold initLaw
  rw [lintegral_map hF (by fun_prop), lintegral_prod _ hF'.aemeasurable,
    Measure.lintegral_compProd hF'.lintegral_prod_right']

lemma lintegral_stepKernel (M : POMDP X Y U) (σ : Measure U) [IsProbabilityMeasure σ]
    (p : X × Y × U) {F : X × Y × U → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂stepKernel M σ p =
      ∫⁻ x, ∫⁻ y, ∫⁻ u, F (x, y, u) ∂σ ∂M.O x ∂M.T (p.1, p.2.2) := by
  have hF' : Measurable fun q : (X × Y) × U => F (q.1.1, q.1.2, q.2) := hF.comp (by fun_prop)
  unfold stepKernel
  rw [Kernel.map_apply _ (by fun_prop), lintegral_map hF (by fun_prop), Kernel.prod_apply,
    lintegral_prod _ hF'.aemeasurable, Kernel.const_apply,
    Kernel.lintegral_compProd _ _ _ hF'.lintegral_prod_right']
  rfl

lemma lintegral_pathMeasure_zero (M : POMDP X Y U) (μ : Measure X) [IsProbabilityMeasure μ]
    (σ : Measure U) [IsProbabilityMeasure σ] {F : X × Y × U → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (ω 0) ∂pathMeasure M μ σ = ∫⁻ z, F z ∂initLaw M μ σ := by
  have hlaw : (pathMeasure M μ σ).map (Preorder.frestrictLe 0) =
      (initLaw M μ σ).map (MeasurableEquiv.piUnique (fun _ : Iic 0 => X × Y × U)).symm := by
    rw [pathMeasure, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  have key := lintegral_map (μ := pathMeasure M μ σ)
    (f := fun h : (Π _ : Iic 0, X × Y × U) => F (h ⟨0, by simp⟩))
    (hF.comp (measurable_pi_apply _)) (by fun_prop : Measurable (Preorder.frestrictLe 0))
  rw [hlaw, lintegral_map (f := fun h : (Π _ : Iic 0, X × Y × U) => F (h ⟨0, by simp⟩))
    (hF.comp (measurable_pi_apply _)) (by fun_prop)] at key
  exact key.symm

/-- One-step Markov property of the exploration path measure. -/
lemma lintegral_markov (M : POMDP X Y U) (μ : Measure X) [IsProbabilityMeasure μ]
    (σ : Measure U) [IsProbabilityMeasure σ] (n : ℕ)
    {Φ : (Π _ : Iic n, X × Y × U) → X × Y × U → ℝ≥0∞} (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ ω, Φ (Preorder.frestrictLe n ω) (ω (n + 1)) ∂pathMeasure M μ σ =
      ∫⁻ ω, ∫⁻ z, Φ (Preorder.frestrictLe n ω) z ∂stepKernel M σ (ω n) ∂pathMeasure M μ σ := by
  haveI : IsProbabilityMeasure (initLaw M μ σ) := by
    unfold initLaw; exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (pathMeasure M μ σ) := by unfold pathMeasure; infer_instance
  have hfr : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => X × Y × U) n) := by fun_prop
  have hc : (pathMeasure M μ σ).map (Preorder.frestrictLe n) ⊗ₘ pathStep M σ n =
      (pathMeasure M μ σ).map (fun x => (Preorder.frestrictLe n x, x (n + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  calc ∫⁻ ω, Φ (Preorder.frestrictLe n ω) (ω (n + 1)) ∂pathMeasure M μ σ
      = ∫⁻ q, Function.uncurry Φ q ∂((pathMeasure M μ σ).map
          (fun x => (Preorder.frestrictLe n x, x (n + 1)))) :=
        (lintegral_map hΦ (hfr.prodMk (measurable_pi_apply (n + 1)))).symm
    _ = ∫⁻ q, Function.uncurry Φ q ∂((pathMeasure M μ σ).map (Preorder.frestrictLe n)
          ⊗ₘ pathStep M σ n) := by rw [hc]
    _ = ∫⁻ p, ∫⁻ z, Φ p z ∂pathStep M σ n p ∂((pathMeasure M μ σ).map (Preorder.frestrictLe n)) :=
        Measure.lintegral_compProd hΦ
    _ = ∫⁻ ω, ∫⁻ z, Φ (Preorder.frestrictLe n ω) z ∂pathStep M σ n (Preorder.frestrictLe n ω)
          ∂pathMeasure M μ σ :=
        lintegral_map (hΦ.lintegral_kernel_prod_right' (κ := pathStep M σ n)) hfr
    _ = _ := rfl

lemma win_succ_iff [DecidableEq Y] [DecidableEq U] (n : ℕ) (ω : ℕ → X × Y × U)
    (ys : Fin (n + 2) → Y) (us : Fin (n + 1) → U) :
    ((fun j : Fin (n + 2) => (ω j).2.1, fun j : Fin (n + 1) => (ω j).2.2) = (ys, us)) ↔
      ((((fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) =
          (Fin.init ys, Fin.init us)) ∧ (ω n).2.2 = us (Fin.last n)) ∧
        (ω (n + 1)).2.1 = ys (Fin.last (n + 1))) := by
  simp only [Prod.mk.injEq, funext_iff, Fin.forall_fin_succ' (n := n + 1),
    Fin.forall_fin_succ' (n := n), Fin.val_castSucc, Fin.val_last, Fin.init]
  tauto

/-- The step-kernel integral of an observation-indicator test function. -/
lemma lintegral_stepKernel_obs [MeasurableSingletonClass Y] [DecidableEq Y] (M : POMDP X Y U)
    (σ : Measure U) [IsProbabilityMeasure σ] (p : X × Y × U) (y0 : Y)
    {h : X → U → ℝ≥0∞} (hh : Measurable (Function.uncurry h)) :
    ∫⁻ z, (if z.2.1 = y0 then h z.1 z.2.2 else 0) ∂stepKernel M σ p =
      ∫⁻ x', M.O x' {y0} * ∫⁻ u', h x' u' ∂σ ∂M.T (p.1, p.2.2) := by
  have hm : Measurable fun z : X × Y × U => if z.2.1 = y0 then h z.1 z.2.2 else 0 :=
    Measurable.ite (measurable_snd.fst (measurableSet_singleton y0))
      (hh.comp (measurable_fst.prodMk measurable_snd.snd)) measurable_const
  rw [lintegral_stepKernel M σ p hm]
  refine lintegral_congr fun x' => ?_
  have : ∀ y : Y, ∫⁻ u, (if y = y0 then h x' u else 0) ∂σ =
      if y = y0 then ∫⁻ u, h x' u ∂σ else 0 := fun y => by split_ifs <;> simp
  simp only [this]
  rw [lintegral_ite_eq, mul_comm]

/-- Finite-dimensional Bayes formula along the path: the window of observations `ys` and actions
`us` occupying times `0..n`, tested against `h (X_n, U_n)`. -/
theorem lintegral_window [MeasurableSingletonClass Y] [MeasurableSingletonClass U]
    [DecidableEq Y] [DecidableEq U] (M : POMDP X Y U) (μ : Measure X) [IsProbabilityMeasure μ]
    (σ : Measure U) [IsProbabilityMeasure σ] (n : ℕ) :
    ∀ (ys : Fin (n + 1) → Y) (us : Fin n → U) {h : X → U → ℝ≥0∞},
      Measurable (Function.uncurry h) →
      ∫⁻ ω, (if (fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) = (ys, us)
          then h (ω n).1 (ω n).2.2 else 0) ∂pathMeasure M μ σ =
        (∏ j, σ {us j}) * ∫⁻ x, ∫⁻ u, h x u ∂σ ∂unnormPost M n μ (ys, us) := by
  induction n with
  | zero =>
    intro ys us h hh
    have hG : Measurable fun x => ∫⁻ u, h x u ∂σ := hh.lintegral_prod_right'
    have hm : Measurable fun z : X × Y × U => if z.2.1 = ys 0 then h z.1 z.2.2 else 0 :=
      Measurable.ite (measurable_snd.fst (measurableSet_singleton _))
        (hh.comp (measurable_fst.prodMk measurable_snd.snd)) measurable_const
    have hpt : ∀ ω : ℕ → X × Y × U,
        (if (fun j : Fin 1 => (ω j).2.1, fun j : Fin 0 => (ω j).2.2) = (ys, us)
          then h (ω 0).1 (ω 0).2.2 else 0) =
        (fun z : X × Y × U => if z.2.1 = ys 0 then h z.1 z.2.2 else 0) (ω 0) := by
      intro ω
      have e : ((fun j : Fin 1 => (ω j).2.1, fun j : Fin 0 => (ω j).2.2) = (ys, us)) ↔
          (ω 0).2.1 = ys 0 := by
        simp [Prod.ext_iff, funext_iff, Fin.forall_fin_one]
      dsimp only
      by_cases h1 : (ω 0).2.1 = ys 0
      · rw [if_pos (e.2 h1), if_pos h1]
      · rw [if_neg (mt e.1 h1), if_neg h1]
    simp only [Nat.cast_zero, hpt]
    rw [lintegral_pathMeasure_zero M μ σ hm, lintegral_initLaw M μ σ hm]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    show _ = ∫⁻ x, ∫⁻ u, h x u ∂σ ∂correct M μ (ys 0)
    rw [lintegral_correct M μ (ys 0) hG]
    refine lintegral_congr fun x => ?_
    have : ∀ y : Y, ∫⁻ u, (if y = ys 0 then h x u else 0) ∂σ =
        if y = ys 0 then ∫⁻ u, h x u ∂σ else 0 := fun y => by split_ifs <;> simp
    simp only [this]
    rw [lintegral_ite_eq, mul_comm]
  | succ n ih =>
    intro ys us h hh
    set y0 := ys (Fin.last (n + 1)) with hy0
    set u0 := us (Fin.last n) with hu0
    let K : X → U → ℝ≥0∞ := fun x u => ∫⁻ x', M.O x' {y0} * ∫⁻ u', h x' u' ∂σ ∂M.T (x, u)
    have hGm : Measurable fun x' => M.O x' {y0} * ∫⁻ u', h x' u' ∂σ :=
      (M.O.measurable_coe (measurableSet_singleton y0)).mul hh.lintegral_prod_right'
    have hK0 : Measurable fun x => K x u0 :=
      (hGm.lintegral_kernel (κ := M.T)).comp (measurable_id.prodMk measurable_const)
    let h' : X → U → ℝ≥0∞ := fun x u => (if u = u0 then 1 else 0) * K x u0
    have hh' : Measurable (Function.uncurry h') :=
      (Measurable.ite (measurable_snd (measurableSet_singleton u0)) measurable_const
        measurable_const).mul (hK0.comp measurable_fst)
    -- the window indicator splits into the old window, the action `U_n`, and `Y_{n+1}`
    let wf : (Π _ : Iic n, X × Y × U) → Window Y U n := fun p =>
      (fun j : Fin (n + 1) => (p ⟨j, by simp only [Finset.mem_Iic]; omega⟩).2.1,
          fun j : Fin n => (p ⟨j, by simp only [Finset.mem_Iic]; omega⟩).2.2)
    have hwf : Measurable wf :=
      Measurable.prodMk (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).snd.fst)
        (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).snd.snd)
    let A : (Π _ : Iic n, X × Y × U) → ℝ≥0∞ := fun p =>
      if wf p = (Fin.init ys, Fin.init us) ∧ (p ⟨n, by simp⟩).2.2 = u0 then 1 else 0
    have hAm : Measurable A :=
      Measurable.ite ((hwf (measurableSet_singleton _)).inter
        ((measurable_pi_apply _).snd.snd (measurableSet_singleton u0))) measurable_const
        measurable_const
    let Φ : (Π _ : Iic n, X × Y × U) → X × Y × U → ℝ≥0∞ := fun p z =>
      A p * (if z.2.1 = y0 then h z.1 z.2.2 else 0)
    have hFm : Measurable fun z : X × Y × U => if z.2.1 = y0 then h z.1 z.2.2 else 0 :=
      Measurable.ite (measurable_snd.fst (measurableSet_singleton _))
        (hh.comp (measurable_fst.prodMk measurable_snd.snd)) measurable_const
    have hΦ : Measurable (Function.uncurry Φ) :=
      (hAm.comp measurable_fst).mul (hFm.comp measurable_snd)
    have hpt : ∀ ω : ℕ → X × Y × U,
        (if (fun j : Fin (n + 2) => (ω j).2.1, fun j : Fin (n + 1) => (ω j).2.2) = (ys, us)
          then h (ω (n + 1 : ℕ)).1 (ω (n + 1 : ℕ)).2.2 else 0) =
        Φ (Preorder.frestrictLe n ω) (ω (n + 1)) := by
      intro ω
      have e := win_succ_iff n ω ys us
      show _ = (if ((fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) =
          (Fin.init ys, Fin.init us) ∧ (ω n).2.2 = u0) then 1 else 0) *
          (if (ω (n + 1)).2.1 = y0 then h (ω (n + 1)).1 (ω (n + 1)).2.2 else 0)
      by_cases h1 : ((fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) =
          (Fin.init ys, Fin.init us) ∧ (ω n).2.2 = u0)
      · by_cases h2 : (ω (n + 1)).2.1 = y0
        · rw [if_pos (e.2 ⟨h1, h2⟩), if_pos h1, if_pos h2, one_mul]
        · rw [if_neg (mt e.1 (fun h => h2 h.2)), if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg (mt e.1 (fun h => h1 h.1)), if_neg h1, zero_mul]
    have hpt2 : ∀ ω : ℕ → X × Y × U,
        ∫⁻ z, Φ (Preorder.frestrictLe n ω) z ∂stepKernel M σ (ω n) =
        (if (fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) =
            (Fin.init ys, Fin.init us) then h' (ω n).1 (ω n).2.2 else 0) := by
      intro ω
      rw [lintegral_const_mul _ hFm, lintegral_stepKernel_obs M σ (ω n) y0 hh]
      show (if ((fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) =
          (Fin.init ys, Fin.init us) ∧ (ω n).2.2 = u0) then 1 else 0) * K (ω n).1 (ω n).2.2 = _
      by_cases h1 : (fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) =
          (Fin.init ys, Fin.init us)
      · by_cases h2 : (ω n).2.2 = u0
        · rw [if_pos ⟨h1, h2⟩, if_pos h1]
          show _ = (if (ω n).2.2 = u0 then 1 else 0) * K (ω n).1 u0
          rw [if_pos h2, h2]
        · rw [if_neg (fun h => h2 h.2), if_pos h1]
          show _ = (if (ω n).2.2 = u0 then 1 else 0) * K (ω n).1 u0
          rw [if_neg h2, zero_mul, zero_mul]
      · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]
    simp only [hpt]
    rw [lintegral_markov M μ σ n hΦ]
    simp only [hpt2]
    rw [ih (Fin.init ys) (Fin.init us) hh']
    have hin : ∀ x, ∫⁻ u, h' x u ∂σ = σ {u0} * K x u0 := fun x => by
      have hi : Measurable (fun u : U => if u = u0 then (1 : ℝ≥0∞) else 0) :=
        Measurable.ite (measurableSet_singleton u0) measurable_const measurable_const
      simp only [h']
      rw [lintegral_mul_const _ hi, lintegral_ite_eq, one_mul]
    simp only [hin]
    rw [lintegral_const_mul _ hK0, unnormPost_succ, ← hy0, ← hu0,
      lintegral_correct M _ y0 (g := fun x => ∫⁻ u, h x u ∂σ) hh.lintegral_prod_right',
      lintegral_predict M _ u0 hGm, Fin.prod_univ_castSucc, ← hu0]
    simp only [Fin.init, K]
    ring

/-- The window statistic `(Y_0..Y_n, U_0..U_{n-1})` of a path. -/
lemma measurable_wvec (n : ℕ) : Measurable (fun ω : ℕ → X × Y × U =>
    ((fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) : Window Y U n)) :=
  Measurable.prodMk (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).snd.fst)
    (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).snd.snd)

lemma measurableSet_V [MeasurableSingletonClass Y] [MeasurableSingletonClass U] (n : ℕ)
    (ys : Fin (n + 1) → Y) (us : Fin n → U) (u : U) :
    MeasurableSet {ω : ℕ → X × Y × U | (fun j : Fin (n + 1) => (ω j).2.1,
      fun j : Fin n => (ω j).2.2) = (ys, us) ∧ (ω n).2.2 = u} :=
  (measurable_wvec n (measurableSet_singleton (ys, us))).inter
    ((measurable_pi_apply n).snd.snd (measurableSet_singleton u))

lemma measurable_window_next [MeasurableSingletonClass Y] [MeasurableSingletonClass U]
    [DecidableEq Y] [DecidableEq U] (n : ℕ) (ys : Fin (n + 1) → Y) (us : Fin n → U) (u : U)
    {R : X → Y → ℝ} (hR : Measurable (Function.uncurry R)) :
    Measurable (fun ω : ℕ → X × Y × U => if (fun j : Fin (n + 1) => (ω j).2.1,
      fun j : Fin n => (ω j).2.2) = (ys, us) ∧ (ω n).2.2 = u then R (ω n).1 (ω (n + 1)).2.1
      else 0) :=
  Measurable.ite (measurableSet_V n ys us u)
    (hR.comp ((measurable_pi_apply n).fst.prodMk (measurable_pi_apply (n + 1)).snd.fst))
    measurable_const

/-- Bayes formula with the action at time `n` and the next observation. -/
theorem lintegral_window_next [MeasurableSingletonClass Y] [MeasurableSingletonClass U]
    [DecidableEq Y] [DecidableEq U] (M : POMDP X Y U) (μ : Measure X) [IsProbabilityMeasure μ]
    (σ : Measure U) [IsProbabilityMeasure σ] (n : ℕ) (ys : Fin (n + 1) → Y) (us : Fin n → U)
    (u : U) {F : X → Y → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    ∫⁻ ω, (if (fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) = (ys, us) ∧
        (ω n).2.2 = u then F (ω n).1 (ω (n + 1)).2.1 else 0) ∂pathMeasure M μ σ =
      (∏ j, σ {us j}) * (σ {u} * ∫⁻ x, ∫⁻ x', ∫⁻ y', F x y' ∂M.O x' ∂M.T (x, u)
        ∂unnormPost M n μ (ys, us)) := by
  let wf : (Π _ : Iic n, X × Y × U) → Window Y U n := fun p =>
    (fun j : Fin (n + 1) => (p ⟨j, by simp only [Finset.mem_Iic]; omega⟩).2.1,
        fun j : Fin n => (p ⟨j, by simp only [Finset.mem_Iic]; omega⟩).2.2)
  have hwf : Measurable wf :=
    Measurable.prodMk (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).snd.fst)
      (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).snd.snd)
  let A : (Π _ : Iic n, X × Y × U) → ℝ≥0∞ := fun p =>
    if wf p = (ys, us) ∧ (p ⟨n, by simp⟩).2.2 = u then 1 else 0
  have hAm : Measurable A :=
    Measurable.ite ((hwf (measurableSet_singleton _)).inter
      ((measurable_pi_apply _).snd.snd (measurableSet_singleton u))) measurable_const
      measurable_const
  let Φ : (Π _ : Iic n, X × Y × U) → X × Y × U → ℝ≥0∞ := fun p z =>
    A p * F (p ⟨n, by simp⟩).1 z.2.1
  have hpn : Measurable fun p : (Π _ : Iic n, X × Y × U) => (p ⟨n, by simp⟩).1 :=
    (measurable_pi_apply _).fst
  have hΦ : Measurable (Function.uncurry Φ) :=
    (hAm.comp measurable_fst).mul (hF.comp
      ((hpn.comp measurable_fst).prodMk measurable_snd.snd.fst))
  have hG : Measurable fun q : X × X => ∫⁻ y', F q.1 y' ∂M.O q.2 :=
    (hF.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right'
      (κ := M.O.comap Prod.snd measurable_snd)
  let Kf : X → U → ℝ≥0∞ := fun x v => ∫⁻ x', ∫⁻ y', F x y' ∂M.O x' ∂M.T (x, v)
  have hKf : Measurable fun x => Kf x u :=
    hG.lintegral_kernel_prod_right'
      (κ := M.T.comap (fun x => (x, u)) (measurable_id.prodMk measurable_const))
  let h' : X → U → ℝ≥0∞ := fun x v => (if v = u then 1 else 0) * Kf x u
  have hh' : Measurable (Function.uncurry h') :=
    (Measurable.ite (measurable_snd (measurableSet_singleton u)) measurable_const
      measurable_const).mul (hKf.comp measurable_fst)
  have hpt : ∀ ω : ℕ → X × Y × U,
      (if (fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) = (ys, us) ∧
        (ω n).2.2 = u then F (ω n).1 (ω (n + 1)).2.1 else 0) =
      Φ (Preorder.frestrictLe n ω) (ω (n + 1)) := by
    intro ω
    show _ = (if ((fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) = (ys, us) ∧
        (ω n).2.2 = u) then 1 else 0) * F (ω n).1 (ω (n + 1)).2.1
    by_cases h1 : ((fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) = (ys, us) ∧
        (ω n).2.2 = u)
    · rw [if_pos h1, if_pos h1, one_mul]
    · rw [if_neg h1, if_neg h1, zero_mul]
  have hpt2 : ∀ ω : ℕ → X × Y × U,
      ∫⁻ z, Φ (Preorder.frestrictLe n ω) z ∂stepKernel M σ (ω n) =
      (if (fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) = (ys, us)
        then h' (ω n).1 (ω n).2.2 else 0) := by
    intro ω
    have hFz : Measurable fun z : X × Y × U => F (ω n).1 z.2.1 :=
      hF.comp (measurable_const.prodMk measurable_snd.fst)
    show ∫⁻ z, A (Preorder.frestrictLe n ω) * F (ω n).1 z.2.1 ∂stepKernel M σ (ω n) = _
    rw [lintegral_const_mul _ hFz, lintegral_stepKernel M σ (ω n) hFz]
    simp only [lintegral_const, measure_univ, mul_one]
    show (if ((fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) = (ys, us) ∧
        (ω n).2.2 = u) then 1 else 0) * Kf (ω n).1 (ω n).2.2 = _
    by_cases h1 : (fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) = (ys, us)
    · by_cases h2 : (ω n).2.2 = u
      · rw [if_pos ⟨h1, h2⟩, if_pos h1]
        show _ = (if (ω n).2.2 = u then 1 else 0) * Kf (ω n).1 u
        rw [if_pos h2, h2]
      · rw [if_neg (fun h => h2 h.2), if_pos h1]
        show _ = (if (ω n).2.2 = u then 1 else 0) * Kf (ω n).1 u
        rw [if_neg h2, zero_mul, zero_mul]
    · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]
  simp only [hpt]
  rw [lintegral_markov M μ σ n hΦ]
  simp only [hpt2]
  rw [lintegral_window M μ σ n ys us hh']
  have hi : Measurable (fun v : U => if v = u then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_singleton u) measurable_const measurable_const
  have hin : ∀ x, ∫⁻ v, h' x v ∂σ = σ {u} * Kf x u := fun x => by
    simp only [h']
    rw [lintegral_mul_const _ hi, lintegral_ite_eq, one_mul]
  simp only [hin]
  rw [lintegral_const_mul _ hKf]

lemma integral_window_next [MeasurableSingletonClass Y] [MeasurableSingletonClass U]
    [DecidableEq Y] [DecidableEq U] (M : POMDP X Y U) (μ : Measure X) [IsProbabilityMeasure μ]
    (σ : Measure U) [IsProbabilityMeasure σ] (n : ℕ) (ys : Fin (n + 1) → Y) (us : Fin n → U)
    (u : U) {R : X → Y → ℝ} (hR : Measurable (Function.uncurry R)) (h0 : ∀ x y, 0 ≤ R x y) :
    ∫ ω, (if (fun j : Fin (n + 1) => (ω j).2.1, fun j : Fin n => (ω j).2.2) = (ys, us) ∧
        (ω n).2.2 = u then R (ω n).1 (ω (n + 1)).2.1 else 0) ∂pathMeasure M μ σ =
      ((∏ j, σ {us j}) * (σ {u} * ∫⁻ x, ∫⁻ x', ∫⁻ y', ENNReal.ofReal (R x y') ∂M.O x'
        ∂M.T (x, u) ∂unnormPost M n μ (ys, us))).toReal := by
  have hmF : Measurable (Function.uncurry fun x y' => ENNReal.ofReal (R x y')) :=
    ENNReal.measurable_ofReal.comp hR
  have e := lintegral_window_next M μ σ n ys us u hmF
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => by
      simp only [Pi.zero_apply]
      split_ifs
      · exact h0 _ _
      · exact le_rfl) (measurable_window_next n ys us u hR).aestronglyMeasurable, ← e]
  congr 1
  refine lintegral_congr fun ω => ?_
  split_ifs <;> simp

lemma correct_univ (M : POMDP X Y U) [MeasurableSingletonClass Y] (μ : Measure X) (y : Y) :
    correct M μ y Set.univ = ∫⁻ x, M.O x {y} ∂μ := by
  unfold correct
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

lemma isFiniteMeasure_correct (M : POMDP X Y U) [MeasurableSingletonClass Y] (μ : Measure X)
    [IsFiniteMeasure μ] (y : Y) : IsFiniteMeasure (correct M μ y) := by
  refine ⟨?_⟩
  rw [correct_univ]
  calc ∫⁻ x, M.O x {y} ∂μ ≤ ∫⁻ _x, 1 ∂μ := lintegral_mono fun x => prob_le_one
    _ < ⊤ := by rw [lintegral_one]; exact measure_lt_top μ _

lemma isFiniteMeasure_predict (M : POMDP X Y U) (μ : Measure X) [IsFiniteMeasure μ] (u : U) :
    IsFiniteMeasure (predict M μ u) := by
  refine ⟨?_⟩
  unfold predict
  have hm : Measurable fun x : X => M.T (x, u) :=
    (M.T.measurable).comp (measurable_id.prodMk measurable_const)
  rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable]
  simp only [measure_univ, lintegral_one]
  exact measure_lt_top μ _

lemma isFiniteMeasure_unnormPost (M : POMDP X Y U) [MeasurableSingletonClass Y] (n : ℕ) :
    ∀ (π : Measure X) [IsFiniteMeasure π] (I : Window Y U n),
      IsFiniteMeasure (unnormPost M n π I) := by
  induction n with
  | zero => intro π _ I; exact isFiniteMeasure_correct M π _
  | succ n ih =>
    intro π _ I
    haveI := isFiniteMeasure_correct M π (I.1 0)
    haveI := isFiniteMeasure_predict M (correct M π (I.1 0)) (I.2 0)
    exact ih _ _

lemma winAt_self {N : ℕ} (ω : ℕ → X × Y × U) :
    winAt (N := N) ω N = (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) := by
  simp [winAt]

lemma winAt_next {N : ℕ} (ω : ℕ → X × Y × U) (ys : Fin (N + 1) → Y) (us : Fin N → U) (u : U)
    (h1 : (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) = (ys, us))
    (h2 : (ω N).2.2 = u) :
    winAt (N := N) ω (N + 1) = shift (ys, us) u (ω (N + 1)).2.1 := by
  rw [← h1, ← h2]
  have e : ∀ k : ℕ, N + 1 - N + k = k + 1 := fun k => by omega
  simp only [winAt, shift, e, Prod.mk.injEq]
  constructor
  · funext j
    simp only [Fin.tail, Fin.snoc, Fin.val_succ, Fin.coe_castLT, cast_eq]
    split_ifs with hj
    · rfl
    · rw [show (j : ℕ) + 1 = N + 1 by omega]
  · funext j
    simp only [Fin.tail, Fin.snoc, Fin.val_succ, Fin.coe_castLT, cast_eq]
    split_ifs with hj
    · rfl
    · rw [show (j : ℕ) + 1 = N by omega]

lemma alg_C4 {ι : Type*} [Fintype ι] (β kr mr Ic B : ℝ) (w g : ι → ℝ)
    (h0 : mr = 0 → (∀ y, w y = 0) ∧ Ic = 0) :
    ∑ y, β * g y * (kr * w y) - (β * ∑ y, mr⁻¹ * w y * g y + mr⁻¹ * Ic + B) * (kr * mr)
      + kr * (Ic + B * mr) = 0 := by
  by_cases hm : mr = 0
  · obtain ⟨h1, h2⟩ := h0 hm
    simp [hm, h1, h2]
  · have e1 : ∑ y, β * g y * (kr * w y) = β * kr * ∑ y, w y * g y := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    have e2 : ∑ y, mr⁻¹ * w y * g y = mr⁻¹ * ∑ y, w y * g y := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    rw [e1, e2]
    field_simp
    ring

/-- (C4) Bayes identity: the stationary-start mean of `r*` on the visit set of `(I, u)` is zero. -/
theorem C4 {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U) (N : ℕ) (σ : Measure U) [IsProbabilityMeasure σ]
    (πs : Measure X) [IsProbabilityMeasure πs] (I : Window Y U N) (u : U) :
    ∫ ω, (if winAt (N := N) ω N = I ∧ (ω N).2.2 = u then rStar M πs ω 0 I u else 0)
      ∂pathMeasure M πs σ = 0 := by
  obtain ⟨ys, us⟩ := I
  obtain ⟨B0, hB0⟩ := M.c_bdd
  have hB : ∀ x v, |M.c x v| ≤ |B0| := fun x v => (hB0 x v).trans (le_abs_self _)
  generalize hBdef : |B0| = B at hB
  haveI : IsProbabilityMeasure (initLaw M πs σ) := by
    unfold initLaw; exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (pathMeasure M πs σ) := by unfold pathMeasure; infer_instance
  obtain ⟨ν, hν⟩ : ∃ ν, ν = unnormPost M N πs (ys, us) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure ν := hν ▸ isFiniteMeasure_unnormPost M N πs (ys, us)
  obtain ⟨g, hg⟩ : ∃ g : Y → ℝ, g = fun y => ⨅ v : U, qStar M πs (shift (ys, us) u y) v :=
    ⟨_, rfl⟩
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = M.β * ∑ y : Y, Pstar M πs (ys, us) u y * g y := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = Cstar M πs (ys, us) u := ⟨_, rfl⟩
  have hpt : ∀ ω : ℕ → X × Y × U,
      (if winAt (N := N) ω N = (ys, us) ∧ (ω N).2.2 = u then rStar M πs ω 0 (ys, us) u
        else 0) =
      ∑ y, M.β * g y * (if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) =
          (ys, us) ∧ (ω N).2.2 = u then (if (ω (N + 1)).2.1 = y then (1 : ℝ) else 0) else 0)
        - (K1 + K2 + B) * (if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) =
          (ys, us) ∧ (ω N).2.2 = u then (1 : ℝ) else 0)
        + (if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) =
          (ys, us) ∧ (ω N).2.2 = u then M.c (ω N).1 u + B else 0) := by
    intro ω
    rw [winAt_self]
    by_cases hc : ((fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) = (ys, us) ∧
        (ω N).2.2 = u)
    · simp only [if_pos hc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      subst hg hK1 hK2
      simp only [rStar, Nat.add_zero]
      rw [winAt_next ω ys us u hc.1 hc.2]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    · simp only [if_neg hc, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
  have hint : ∀ f : (ℕ → X × Y × U) → ℝ, Measurable f → ∀ C : ℝ, (∀ ω, |f ω| ≤ C) →
      Integrable f (pathMeasure M πs σ) := fun f hf C hC =>
    Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  have hRy : ∀ y : Y, Measurable (Function.uncurry fun (_ : X) (y' : Y) =>
      if y' = y then (1 : ℝ) else 0) := fun y =>
    Measurable.ite (measurable_snd (measurableSet_singleton y)) measurable_const measurable_const
  have hR1 : Measurable (Function.uncurry fun (_ : X) (_ : Y) => (1 : ℝ)) := measurable_const
  have hRc : Measurable (Function.uncurry fun (x : X) (_ : Y) => M.c x u + B) :=
    ((M.c_meas u).comp measurable_fst).add measurable_const
  have iy : ∀ y, Integrable (fun ω : ℕ → X × Y × U =>
      if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) = (ys, us) ∧
        (ω N).2.2 = u then (if (ω (N + 1)).2.1 = y then (1 : ℝ) else 0) else 0)
      (pathMeasure M πs σ) := fun y =>
    hint _ (measurable_window_next N ys us u (hRy y)) 1 fun ω => by
      beta_reduce; split_ifs <;> simp
  have i1 : Integrable (fun ω : ℕ → X × Y × U =>
      if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) = (ys, us) ∧
        (ω N).2.2 = u then (1 : ℝ) else 0) (pathMeasure M πs σ) :=
    hint _ (measurable_window_next N ys us u hR1) 1 fun ω => by
      beta_reduce; split_ifs <;> simp
  have ic : Integrable (fun ω : ℕ → X × Y × U =>
      if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) = (ys, us) ∧
        (ω N).2.2 = u then M.c (ω N).1 u + B else 0) (pathMeasure M πs σ) :=
    hint _ (measurable_window_next N ys us u hRc) (2 * B) fun ω => by
      beta_reduce
      have := abs_le.mp (hB (ω N).1 u)
      split_ifs
      · rw [abs_le]; constructor <;> linarith
      · simp only [abs_zero]; linarith
  have hconv : ∀ y y' : Y, ENNReal.ofReal (if y' = y then (1 : ℝ) else 0) =
      if y' = y then 1 else 0 := fun y y' => by split_ifs <;> simp
  have Ey : ∀ y, ∫ ω, (if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) =
        (ys, us) ∧ (ω N).2.2 = u then (if (ω (N + 1)).2.1 = y then (1 : ℝ) else 0) else 0)
        ∂pathMeasure M πs σ =
      ((∏ j, σ {us j}).toReal * (σ {u}).toReal) *
        (∫⁻ x, ∫⁻ x', M.O x' {y} ∂M.T (x, u) ∂ν).toReal := by
    intro y
    have e := integral_window_next M πs σ N ys us u (hRy y)
      (fun _ _ => by beta_reduce; split_ifs <;> norm_num)
    beta_reduce at e
    rw [e, ← hν]
    simp only [hconv, lintegral_ite_eq, one_mul, ENNReal.toReal_mul]
    ring
  have E1 : ∫ ω, (if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) =
        (ys, us) ∧ (ω N).2.2 = u then (1 : ℝ) else 0) ∂pathMeasure M πs σ =
      ((∏ j, σ {us j}).toReal * (σ {u}).toReal) * (ν Set.univ).toReal := by
    have e := integral_window_next M πs σ N ys us u hR1 (fun _ _ => zero_le_one)
    beta_reduce at e
    rw [e, ← hν]
    simp only [ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one, one_mul,
      ENNReal.toReal_mul]
    ring
  have Ec : ∫ ω, (if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) =
        (ys, us) ∧ (ω N).2.2 = u then M.c (ω N).1 u + B else 0) ∂pathMeasure M πs σ =
      ((∏ j, σ {us j}).toReal * (σ {u}).toReal) *
        (∫ x, M.c x u ∂ν + B * (ν Set.univ).toReal) := by
    have e := integral_window_next M πs σ N ys us u hRc
      (fun x _ => by beta_reduce; have := abs_le.mp (hB x u); linarith)
    beta_reduce at e
    rw [e, ← hν]
    simp only [lintegral_const, measure_univ, mul_one, ENNReal.toReal_mul]
    have hcm : Measurable fun x => M.c x u + B := (M.c_meas u).add measurable_const
    have hci : Integrable (fun x => M.c x u) ν :=
      Integrable.mono' (integrable_const B) (M.c_meas u).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB x u)
    have h1 : ∫ x, M.c x u + B ∂ν = (∫⁻ x, ENNReal.ofReal (M.c x u + B) ∂ν).toReal :=
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by
        have := abs_le.mp (hB x u); simp only [Pi.zero_apply]; linarith) hcm.aestronglyMeasurable
    rw [← h1, integral_add hci (integrable_const B), integral_const, smul_eq_mul, measureReal_def]
    ring
  have PS : ∀ y, Pstar M πs (ys, us) u y =
      (ν Set.univ).toReal⁻¹ * (∫⁻ x, ∫⁻ x', M.O x' {y} ∂M.T (x, u) ∂ν).toReal := by
    intro y
    simp only [Pstar, predY, obsProb, post, normalize, ← hν]
    rw [correct_univ, lintegral_predict M _ u (M.O.measurable_coe (measurableSet_singleton y))]
    simp only [lintegral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have CS : Cstar M πs (ys, us) u = (ν Set.univ).toReal⁻¹ * ∫ x, M.c x u ∂ν := by
    simp only [Cstar, chat, beliefCost, post, normalize, ← hν]
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  simp only [hpt]
  have hS : Integrable (fun ω : ℕ → X × Y × U => ∑ y, M.β * g y * (if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) = (ys, us) ∧ (ω N).2.2 = u
      then (if (ω (N + 1)).2.1 = y then (1 : ℝ) else 0) else 0)) (pathMeasure M πs σ) :=
    integrable_finset_sum _ fun y _ => (iy y).const_mul _
  have hK : Integrable (fun ω : ℕ → X × Y × U => (K1 + K2 + B) * (if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) = (ys, us) ∧ (ω N).2.2 = u
      then (1 : ℝ) else 0)) (pathMeasure M πs σ) := i1.const_mul _
  have hSK : Integrable (fun ω : ℕ → X × Y × U => ∑ y, M.β * g y * (if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) = (ys, us) ∧ (ω N).2.2 = u
      then (if (ω (N + 1)).2.1 = y then (1 : ℝ) else 0) else 0) - (K1 + K2 + B) * (if (fun j : Fin (N + 1) => (ω j).2.1, fun j : Fin N => (ω j).2.2) = (ys, us) ∧ (ω N).2.2 = u
      then (1 : ℝ) else 0)) (pathMeasure M πs σ) := hS.sub hK
  rw [integral_add hSK ic, integral_sub hS hK,
    integral_finset_sum _ fun y _ => (iy y).const_mul _, integral_const_mul]
  simp only [integral_const_mul, Ey, E1, Ec]
  rw [hK1, hK2, CS]
  simp only [PS]
  refine alg_C4 M.β ((∏ j, σ {us j}).toReal * (σ {u}).toReal) (ν Set.univ).toReal
    (∫ x, M.c x u ∂ν) B (fun y => (∫⁻ x, ∫⁻ x', M.O x' {y} ∂M.T (x, u) ∂ν).toReal) g ?_
  intro hm
  have hν0 : ν = 0 := by
    rw [ENNReal.toReal_eq_zero_iff] at hm
    rcases hm with hm | hm
    · exact Measure.measure_univ_eq_zero.mp hm
    · exact absurd hm (measure_ne_top ν _)
  subst hν0
  exact ⟨fun y => by simp, by simp⟩

end FiniteMemQL.Convergence.AppAAux


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FiniteMemQL.Convergence.AppAAux

open FiniteMemQL.Convergence

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

lemma winAt_pshift {N : ℕ} (ω : ℕ → X × Y × U) (k t : ℕ) (ht : N ≤ t) :
    winAt (N := N) (fun s => ω (k + s)) t = winAt (N := N) ω (k + t) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · show (ω (k + (t - N + (j : ℕ)))).2.1 = (ω (k + t - N + (j : ℕ))).2.1
    rw [show k + (t - N + (j : ℕ)) = k + t - N + (j : ℕ) by omega]
  · show (ω (k + (t - N + (j : ℕ)))).2.2 = (ω (k + t - N + (j : ℕ))).2.2
    rw [show k + (t - N + (j : ℕ)) = k + t - N + (j : ℕ) by omega]

lemma winAt_pshift' {N : ℕ} (ω : ℕ → X × Y × U) (k : ℕ) :
    winAt (N := N) (fun s => ω (k + s)) N = winAt (N := N) ω (N + k) := by
  rw [winAt_pshift ω k N le_rfl, Nat.add_comm]

lemma rStar_pshift [Fintype Y] [Fintype U] (M : POMDP X Y U) {N : ℕ} (πs : Measure X)
    (ω : ℕ → X × Y × U) (k : ℕ) (I : Window Y U N) (u : U) :
    rStar M πs ω k I u = rStar M πs (fun s => ω (k + s)) 0 I u := by
  simp only [rStar, Nat.add_zero]
  rw [winAt_pshift ω k (N + 1) (by omega), show k + (N + 1) = N + k + 1 by omega,
    show k + N = N + k by omega]

lemma measurable_winAt {N : ℕ} (t : ℕ) :
    Measurable (fun ω : ℕ → X × Y × U => winAt (N := N) ω t) :=
  Measurable.prodMk (measurable_pi_lambda _ fun _ => ((measurable_pi_apply _).snd).fst)
    (measurable_pi_lambda _ fun _ => ((measurable_pi_apply _).snd).snd)

/-- Closed form of the auxiliary iterate: after `n` steps, `v` is the sum of `r*` over the visits
to `(I, u)` divided by one plus the number of visits. -/
lemma vIter_eq [Fintype Y] [DecidableEq Y] [DecidableEq U] [Fintype U] (M : POMDP X Y U)
    {N : ℕ} (πs : Measure X) (ω : ℕ → X × Y × U) (I : Window Y U N) (u : U) (n : ℕ) :
    vIter M πs ω n I u =
      (∑ k ∈ range n, if winAt (N := N) ω (N + k) = I ∧ (ω (N + k)).2.2 = u
          then rStar M πs ω k I u else 0) /
        ((∑ k ∈ range n, if winAt (N := N) ω (N + k) = I ∧ (ω (N + k)).2.2 = u
          then (1 : ℝ) else 0) + 1) := by
  induction n with
  | zero => simp [vIter]
  | succ n ih =>
    have hC : 0 ≤ ∑ k ∈ range n, if winAt (N := N) ω (N + k) = I ∧ (ω (N + k)).2.2 = u
        then (1 : ℝ) else 0 :=
      Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num
    have hvis : (visits ω n I u : ℝ) = ∑ k ∈ range (n + 1),
        if winAt (N := N) ω (N + k) = I ∧ (ω (N + k)).2.2 = u then (1 : ℝ) else 0 := by
      simp only [visits]
      rw [Finset.natCast_card_filter]
    show (if winAt (N := N) ω (N + n) = I ∧ (ω (N + n)).2.2 = u then
        (1 - 1 / (1 + (visits ω n I u : ℝ))) * vIter M πs ω n I u
          + 1 / (1 + (visits ω n I u : ℝ)) * rStar M πs ω n I u
      else vIter M πs ω n I u) = _
    rw [hvis, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    split_ifs with h
    · set C := ∑ k ∈ range n, if winAt (N := N) ω (N + k) = I ∧ (ω (N + k)).2.2 = u
        then (1 : ℝ) else 0
      have h1 : C + 1 ≠ 0 := by linarith
      have h2 : 1 + (C + 1) ≠ 0 := by linarith
      have h3 : C + 1 + 1 ≠ 0 := by linarith
      field_simp
      ring
    · simp

/-- Assembly of Appendix A from three child facts:
(C3a) the ergodic law of large numbers for the exploration path measure from any start,
(C3b) path events of stationary probability zero occur only finitely often along the shifts,
(C4) the stationary mean of `r*` on the visit set of `(I, u)` vanishes (Bayes identity). -/
theorem appA_main {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    (N : ℕ) (σ : Measure U) [IsProbabilityMeasure σ]
    (πs : Measure X) [IsProbabilityMeasure πs]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hvisit : ∀ᵐ ω ∂pathMeasure M μ σ, ∀ (I : Window Y U N) (u : U),
      ∃ᶠ t in atTop, winAt (N := N) ω t = I ∧ (ω t).2.2 = u)
    (hC3a : ∀ G : (ℕ → X × Y × U) → ℝ, Measurable G → (∃ B : ℝ, ∀ ω, |G ω| ≤ B) →
      ∀ᵐ ω ∂pathMeasure M μ σ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ k ∈ range n, G (fun t => ω (k + t))) atTop (𝓝 (∫ ω, G ω ∂pathMeasure M πs σ)))
    (hC3b : ∀ A : Set (ℕ → X × Y × U), MeasurableSet A → pathMeasure M πs σ A = 0 →
      ∀ᵐ ω ∂pathMeasure M μ σ, ∀ᶠ k in atTop, (fun t => ω (k + t)) ∉ A)
    (hC4 : ∀ (I : Window Y U N) (u : U), ∫ ω, (if winAt (N := N) ω N = I ∧ (ω N).2.2 = u
      then rStar M πs ω 0 I u else 0) ∂pathMeasure M πs σ = 0) :
    ∀ᵐ ω ∂pathMeasure M μ σ, ∀ (I : Window Y U N) (u : U),
      Tendsto (fun n : ℕ => vIter M πs ω n I u) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (initLaw M πs σ) := by
    unfold initLaw; exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (pathMeasure M πs σ) := by unfold pathMeasure; infer_instance
  obtain ⟨Bc, hBc⟩ := M.c_bdd
  -- the visit set at time `N` of a path
  let A : Window Y U N → U → Set (ℕ → X × Y × U) := fun I u =>
    {ω | winAt (N := N) ω N = I ∧ (ω N).2.2 = u}
  have hAm : ∀ I u, MeasurableSet (A I u) := fun I u =>
    (measurable_winAt (N := N) N (measurableSet_singleton I)).inter
      ((measurable_pi_apply N).snd.snd (measurableSet_singleton u))
  -- `V*` as a function on the finite set of windows
  let g : Window Y U N → ℝ := fun w => ⨅ v : U, qStar M πs w v
  have hgm : Measurable g := measurable_of_countable g
  let Sg : ℝ := ∑ w, |g w|
  have hg : ∀ w, |g w| ≤ Sg := fun w =>
    Finset.single_le_sum (f := fun w => |g w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
  have hrm : ∀ (I : Window Y U N) (u : U), Measurable (fun ω : ℕ → X × Y × U => rStar M πs ω 0 I u) := by
    intro I u
    unfold rStar
    exact (((measurable_const.mul (hgm.comp (measurable_winAt _))).sub measurable_const).add
      ((M.c_meas u).comp (measurable_pi_apply _).fst)).sub measurable_const
  have hrb : ∀ (I : Window Y U N) (u : U) (ω : ℕ → X × Y × U), |rStar M πs ω 0 I u| ≤
      M.β * Sg + |M.β * ∑ y : Y, Pstar M πs I u y * (⨅ v : U, qStar M πs (shift I u y) v)|
        + Bc + |Cstar M πs I u| := by
    intro I u ω
    have h1 : |M.β * g (winAt (N := N) ω (N + 0 + 1))| ≤ M.β * Sg := by
      rw [abs_mul, abs_of_pos M.β_pos]
      exact mul_le_mul_of_nonneg_left (hg _) M.β_pos.le
    have h3 := hBc (ω (N + 0)).1 u
    set K1 := M.β * ∑ y : Y, Pstar M πs I u y * (⨅ v : U, qStar M πs (shift I u y) v)
    set K2 := Cstar M πs I u
    have e : rStar M πs ω 0 I u = M.β * g (winAt (N := N) ω (N + 0 + 1)) - K1
        + M.c (ω (N + 0)).1 u - K2 := rfl
    rw [e]
    have a1 := abs_le.mp h1
    have a3 := abs_le.mp h3
    rw [abs_le]
    constructor <;>
      nlinarith [neg_abs_le K1, le_abs_self K1, neg_abs_le K2, le_abs_self K2]
  -- the two test functions
  let FV : Window Y U N → U → (ℕ → X × Y × U) → ℝ := fun I u ω =>
    if winAt (N := N) ω N = I ∧ (ω N).2.2 = u then (1 : ℝ) else 0
  let FR : Window Y U N → U → (ℕ → X × Y × U) → ℝ := fun I u ω =>
    if winAt (N := N) ω N = I ∧ (ω N).2.2 = u then rStar M πs ω 0 I u else 0
  have hFVm : ∀ I u, Measurable (FV I u) := fun I u =>
    Measurable.ite (hAm I u) measurable_const measurable_const
  have hFRm : ∀ I u, Measurable (FR I u) := fun I u =>
    Measurable.ite (hAm I u) (hrm I u) measurable_const
  have hFVb : ∀ I u, ∃ B : ℝ, ∀ ω, |FV I u ω| ≤ B := fun I u =>
    ⟨1, fun ω => by simp only [FV]; split_ifs <;> norm_num⟩
  have hFRb : ∀ I u, ∃ B : ℝ, ∀ ω, |FR I u ω| ≤ B := fun I u =>
    ⟨max (M.β * Sg + |M.β * ∑ y : Y, Pstar M πs I u y * (⨅ v : U, qStar M πs (shift I u y) v)|
        + Bc + |Cstar M πs I u|) 0, fun ω => by
      simp only [FR]
      split_ifs
      · exact (hrb I u ω).trans (le_max_left _ _)
      · simp⟩
  -- the stationary mean of `FV` is the stationary probability of the visit set
  have hFVint : ∀ I u, ∫ ω, FV I u ω ∂pathMeasure M πs σ = (pathMeasure M πs σ).real (A I u) := by
    intro I u
    have : FV I u = (A I u).indicator 1 := by
      funext ω; simp only [FV, Set.indicator_apply, A, Set.mem_setOf_eq, Pi.one_apply]
    rw [this, integral_indicator_one (hAm I u)]
  have hZ : ∀ I u, ∀ᵐ ω ∂pathMeasure M μ σ, pathMeasure M πs σ (A I u) = 0 →
      ∀ᶠ k in atTop, (fun t => ω (k + t)) ∉ A I u := by
    intro I u
    by_cases h0 : pathMeasure M πs σ (A I u) = 0
    · exact (hC3b _ (hAm I u) h0).mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h h0
  filter_upwards [hvisit, ae_all_iff.2 fun I => ae_all_iff.2 fun u =>
      hC3a (FV I u) (hFVm I u) (hFVb I u),
    ae_all_iff.2 fun I => ae_all_iff.2 fun u => hC3a (FR I u) (hFRm I u) (hFRb I u),
    ae_all_iff.2 fun I => ae_all_iff.2 fun u => hZ I u] with ω hvis hV hR hZω I u
  have hSR : ∀ n, (∑ k ∈ range n, FR I u (fun t => ω (k + t))) =
      ∑ k ∈ range n, if winAt (N := N) ω (N + k) = I ∧ (ω (N + k)).2.2 = u
        then rStar M πs ω k I u else 0 := fun n =>
    Finset.sum_congr rfl fun k _ => by
      simp only [FR, winAt_pshift', ← rStar_pshift, show k + N = N + k from Nat.add_comm k N]
  have hSV : ∀ n, (∑ k ∈ range n, FV I u (fun t => ω (k + t))) =
      ∑ k ∈ range n, if winAt (N := N) ω (N + k) = I ∧ (ω (N + k)).2.2 = u
        then (1 : ℝ) else 0 := fun n =>
    Finset.sum_congr rfl fun k _ => by
      simp only [FV, winAt_pshift', show k + N = N + k from Nat.add_comm k N]
  have hRl := hR I u
  have hVl := hV I u
  simp only [hSR] at hRl
  simp only [hSV] at hVl
  have hR0 : ∫ ω, FR I u ω ∂pathMeasure M πs σ = 0 := hC4 I u
  rw [hR0] at hRl
  rw [hFVint] at hVl
  by_cases h0 : pathMeasure M πs σ (A I u) = 0
  · -- a stationary-null visit set is visited only finitely often: contradicts `hvisit`
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hZω I u h0)
    refine absurd (hvis I u) ?_
    rw [not_frequently]
    refine eventually_atTop.2 ⟨N + K, fun t ht h => hK (t - N) (by omega) ?_⟩
    have e : t - N + N = t := by omega
    show winAt (N := N) (fun s => ω (t - N + s)) N = I ∧ (ω (t - N + N)).2.2 = u
    rw [winAt_pshift ω (t - N) N le_rfl, e]
    exact h
  · have hp : 0 < (pathMeasure M πs σ).real (A I u) :=
      ENNReal.toReal_pos h0 (measure_ne_top _ _)
    have hlim := hRl.div (hVl.add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
      (by rw [add_zero]; exact hp.ne')
    rw [zero_div] at hlim
    refine hlim.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    show (n : ℝ)⁻¹ * _ / ((n : ℝ)⁻¹ * _ + (n : ℝ)⁻¹) = vIter M πs ω n I u
    rw [vIter_eq M πs ω I u n]
    have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (show n ≠ 0 by omega))
    rw [← mul_add_one, mul_div_mul_left _ _ hn']

end FiniteMemQL.Convergence.AppAAux


open MeasureTheory ProbabilityTheory Filter Finset Topology FiniteMemQL.Convergence in
theorem solution {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    (N : ℕ) (σ : Measure U) [IsProbabilityMeasure σ] (hσ : ∀ u : U, 0 < σ {u})
    (hHarris : RiskSensMDP.AverageCost.IsPositiveHarrisRecurrent (explKernel M σ))
    (πs : Measure X) [IsProbabilityMeasure πs] (hπs : Kernel.Invariant (explKernel M σ) πs)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hvisit : ∀ᵐ ω ∂pathMeasure M μ σ, ∀ (I : Window Y U N) (u : U),
      ∃ᶠ t in atTop, winAt (N := N) ω t = I ∧ (ω t).2.2 = u) :
    ∀ᵐ ω ∂pathMeasure M μ σ, ∀ (I : Window Y U N) (u : U),
      Tendsto (fun n : ℕ => vIter M πs ω n I u) atTop (𝓝 0) := by
  haveI : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  exact AppAAux.appA_main M N σ πs μ hvisit
    (fun G hG hB => AppAAux.C3a M σ hHarris.1 πs hπs μ G hG hB)
    (fun A hA h0 => AppAAux.C3b M σ hHarris.1 πs hπs μ A hA h0)
    (fun I u => AppAAux.C4 M N σ πs I u)
