-- Prove2me | solution 1 for CTJMDP.MarkovSuff.corollary_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:53:08.490688+00:00
-- url     : https://prove2.me/submissions/3f8b20b7-9f0e-4c23-9aad-c1037ba3e9ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting
import Theorems.Thm_CTJMDP_MarkovSuff_theorem_3
import Theorems.Thm_CTJMDP_MarkovSuff_eq_31

open CTJMDP.MarkovSuff MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace CTJMDPAuxC5

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

theorem jumpM_singleton {M : Model X A} (hM : M.Standing) (z : X) (a : A) :
    M.jumpM z a {z} = 0 := by
  unfold Model.jumpM
  split_ifs with h
  · exact hM.no_self z a h
  · simp

theorem measurable_jumpM_kernel {M : Model X A} (hM : M.Standing) (z : X) :
    Measurable (fun a => M.jumpM z a) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  exact (hM.measurable S hS).comp (measurable_prodMk_left (x := z))

theorem jumpP_apply {M : Model X A} (hM : M.Standing) (z : X) (p : Measure A) {S : Set X}
    (hS : MeasurableSet S) : jumpP M z p S = ∫⁻ a, M.jumpM z a S ∂p := by
  unfold jumpP
  exact Measure.bind_apply hS (measurable_jumpM_kernel hM z).aemeasurable

theorem jumpP_compl {M : Model X A} [MeasurableSingletonClass X] (hM : M.Standing) (z : X)
    (p : Measure A) : jumpP M z p {z}ᶜ = rateP M z p := by
  rw [jumpP_apply hM z p (measurableSet_singleton z).compl]
  unfold rateP Model.rate
  congr 1; funext a
  have := measure_add_measure_compl (μ := M.jumpM z a) (measurableSet_singleton z)
  rwa [jumpM_singleton hM, zero_add] at this

theorem rateP_le {M : Model X A} {z : X} {p : Measure A} [IsProbabilityMeasure p]
    (hM : M.Standing) (hp : p (M.Aset z)ᶜ = 0) : rateP M z p ≤ ⨆ a ∈ M.Aset z, M.rate z a := by
  unfold rateP
  calc ∫⁻ a, M.rate z a ∂p ≤ ∫⁻ _, (⨆ a ∈ M.Aset z, M.rate z a) ∂p := by
        refine lintegral_mono_ae ?_
        have : ∀ᵐ a ∂p, a ∈ M.Aset z := by
          rw [ae_iff]; exact hp
        filter_upwards [this] with a ha
        exact le_iSup₂ (f := fun a _ => M.rate z a) a ha
    _ = _ := by simp

theorem isFwdSolQ_congr {qQ : X → ℝ → Measure X} {x : X} {Q Q' : ℝ → Measure X}
    (h : ∀ t : ℝ, 0 < t → Q t = Q' t) (hQ : IsFwdSolQ qQ x Q) : IsFwdSolQ qQ x Q' := by
  have hint : ∀ t : ℝ, ∀ g : X → ℝ → Measure X → ℝ≥0∞,
      ∫⁻ s in Ioc (0 : ℝ) t, g x s (Q s) = ∫⁻ s in Ioc (0 : ℝ) t, g x s (Q' s) :=
    fun t g => setLIntegral_congr_fun measurableSet_Ioc (fun s hs => by rw [h s hs.1])
  refine ⟨fun t ht => h t ht ▸ hQ.finite t ht, fun Z hZ => ?_, fun t ht Z hYZ => ?_⟩
  · have e : (fun t : Ioi (0 : ℝ) => Q' t Z) = fun t : Ioi (0 : ℝ) => Q t Z := by
      funext t; rw [h t t.2]
    rw [e]; exact hQ.measurable Z hZ
  · obtain ⟨h1, h2, h3⟩ := hQ.eqn t ht Z hYZ
    have e1 : ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z in Z, qQ z s {z}ᶜ ∂(Q s) =
        ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z in Z, qQ z s {z}ᶜ ∂(Q' s) :=
      setLIntegral_congr_fun measurableSet_Ioc (fun s hs => by rw [h s hs.1])
    have e2 : ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z, qQ z s (Z \ {z}) ∂(Q s) =
        ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z, qQ z s (Z \ {z}) ∂(Q' s) :=
      setLIntegral_congr_fun measurableSet_Ioc (fun s hs => by rw [h s hs.1])
    rw [← h t ht, ← e1, ← e2]
    exact ⟨h1, h2, h3⟩

end CTJMDPAuxC5

open CTJMDPAuxC5

theorem solution {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (P : Measure (Traj X)) (hP : IsLaw M (Measure.dirac x) (markovPol phi) P) :
    IsFwdSol M phi x (stateMarg P) ∧
    (∀ Q : ℝ → Measure X, IsFwdSol M phi x Q →
      ∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z → stateMarg P t Z ≤ Q t Z) ∧
    (∀ s : ℝ, 0 < s → stateMarg P s univ = 1 →
      ∀ Q : ℝ → Measure X, IsFwdSol M phi x Q → (∀ t : ℝ, 0 < t → Q t univ ≤ 1) →
        ∀ t ∈ Ioc (0 : ℝ) s, ∀ Z : Set X, MeasurableSet Z → Q t Z = stateMarg P t Z) ∧
    ((∀ t : ℝ, 0 < t → stateMarg P t univ = 1) →
      ∀ Q : ℝ → Measure X, IsFwdSol M phi x Q → (∀ t : ℝ, 0 < t → Q t univ ≤ 1) →
        ∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z → Q t Z = stateMarg P t Z) := by
  -- `q(z, t) = q̃(z, ϕ_t) ≤ q̄(z)`
  have hbound : ∀ z : X, ∀ t : ℝ, 0 < t → qOf M phi z t {z}ᶜ ≤ ⨆ a ∈ M.Aset z, M.rate z a := by
    intro z t ht
    have := hphi.prob z t ht
    rw [qOf, jumpP_compl hM]
    exact rateP_le hM (hphi.feasible z t ht)
  have hq : IsQFunction (qOf M phi) := by
    refine ⟨fun z t ht => ?_, fun z t ht => ?_, fun Z hZ => ?_⟩
    · refine ⟨?_⟩
      have := hphi.prob z t ht
      have h1 : qOf M phi z t univ = rateP M z (phi z t) := by
        rw [qOf, jumpP_apply hM z _ MeasurableSet.univ]; rfl
      rw [h1]
      exact lt_of_le_of_lt (rateP_le hM (hphi.feasible z t ht)) (hA z)
    · rw [qOf, jumpP_apply hM z _ (measurableSet_singleton z)]
      simp [jumpM_singleton hM]
    · let κ : Kernel (X × Ioi (0:ℝ)) A :=
        ⟨fun p => phi p.1 p.2, Measure.measurable_of_measurable_coe _ fun B hB => hphi.measurable B hB⟩
      have : IsMarkovKernel κ := ⟨fun p => hphi.prob p.1 p.2 p.2.2⟩
      have e : (fun p : X × Ioi (0:ℝ) => qOf M phi p.1 p.2 Z) =
          fun p => ∫⁻ a, M.jumpM p.1 a Z ∂(κ p) := by
        funext p; rw [qOf, jumpP_apply hM _ _ hZ]; rfl
      rw [e]
      exact Measurable.lintegral_kernel_prod_right' (κ := κ)
        (f := fun r : (X × Ioi (0:ℝ)) × A => M.jumpM r.1.1 r.2 Z)
        ((hM.measurable Z hZ).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have h28 : ∀ z : X, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t : ℝ, 0 < t → qOf M phi z t {z}ᶜ ≤ C :=
    fun z => ⟨_, hA z, hbound z⟩
  obtain ⟨-, Pbar, hPbar, hsol, hmin, huniq, huniq2⟩ := theorem_3 (qOf M phi) hq h28 x
  have hagree : ∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z → stateMarg P t Z = Pbar t Z :=
    fun t ht Z hZ => by rw [eq_31 M hM hA x phi hphi P hP t ht Z hZ, hPbar t ht Z hZ]
  have hmeq : ∀ t : ℝ, 0 < t → Pbar t = stateMarg P t :=
    fun t ht => Measure.ext fun Z hZ => (hagree t ht Z hZ).symm
  refine ⟨isFwdSolQ_congr hmeq hsol, ?_, ?_, ?_⟩
  · intro Q hQ t ht Z hZ
    rw [hagree t ht Z hZ]
    exact hmin Q hQ t ht Z hZ
  · intro s hs hs1 Q hQ hle t ht Z hZ
    rw [hagree t ht.1 Z hZ]
    exact huniq s hs (by rw [← hagree s hs univ MeasurableSet.univ]; exact hs1) Q hQ hle t ht Z hZ
  · intro hall Q hQ hle t ht Z hZ
    rw [hagree t ht Z hZ]
    exact huniq2 (fun t ht => by rw [← hagree t ht univ MeasurableSet.univ]; exact hall t ht)
      Q hQ hle t ht Z hZ
