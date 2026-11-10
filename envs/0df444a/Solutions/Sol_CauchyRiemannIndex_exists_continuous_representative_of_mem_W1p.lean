-- Prove2me | solution 1 for CauchyRiemannIndex.exists_continuous_representative_of_mem_W1p
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T16:42:29.698871+00:00
-- url     : https://prove2.me/submissions/3cab9429-f06e-4188-aa35-d52fcf73880c

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Theorems.Thm_CauchyRiemannIndex_enorm_le_w1pNorm_of_isTestSection
import Theorems.Thm_CauchyRiemannIndex_eq_of_continuous_periodic_ae_eq
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Normed



namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- Matrices as continuous linear maps of `ℝ²ⁿ`, continuously in the matrix. -/
def matCLM (n : ℕ) : Mat n →ₗ[ℝ] (Vec n →L[ℝ] Vec n) :=
  (LinearMap.toContinuousLinearMap : (Vec n →ₗ[ℝ] Vec n) ≃ₗ[ℝ] (Vec n →L[ℝ] Vec n)).toLinearMap ∘ₗ
    (Matrix.toEuclideanLin : Mat n ≃ₗ[ℝ] (Vec n →ₗ[ℝ] Vec n)).toLinearMap

lemma matCLM_apply (A : Mat n) (v : Vec n) : matCLM n A v = Matrix.toEuclideanLin A v := rfl

lemma continuous_matCLM : Continuous (matCLM n) := LinearMap.continuous_of_finiteDimensional _

/-- A uniform operator bound for a continuous `1`-periodic matrix loop. -/
lemma exists_bound_loop (Sinf : ℝ → Mat n) (hc : Continuous Sinf) (hper : Function.Periodic Sinf 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t (v : Vec n), ‖Matrix.toEuclideanLin (Sinf t) v‖ ≤ M * ‖v‖ := by
  have hg : Continuous fun t => matCLM n (Sinf t) := continuous_matCLM.comp hc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t v => ?_⟩
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
  rw [← matCLM_apply, hty]
  calc ‖matCLM n (Sinf y) v‖ ≤ ‖matCLM n (Sinf y)‖ * ‖v‖ := (matCLM n (Sinf y)).le_opNorm v
    _ ≤ max C 0 * ‖v‖ := by
      gcongr
      exact (hC y (Set.Ico_subset_Icc_self hy)).trans (le_max_left _ _)

lemma exists_bound_mat (A : Mat n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (v : Vec n), ‖Matrix.toEuclideanLin A v‖ ≤ M * ‖v‖ :=
  ⟨‖matCLM n A‖, norm_nonneg _, fun v => (matCLM n A).le_opNorm v⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous map on `ℝ × ℝ` vanishing for large `|s|` is in `L^p` of the strip. -/
lemma memLp_of_vanish {E : Type*} [NormedAddCommGroup E] (g : ℝ × ℝ → E) (hg : Continuous g)
    (R : ℝ) (hR : ∀ s t, R < |s| → g (s, t) = 0) : MemLp g p cylMeasure := by
  set K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hae : K.indicator g =ᵐ[cylMeasure] g := by
    unfold cylMeasure
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Ico) ?_
    rintro ⟨s, t⟩ ⟨-, ht⟩
    by_cases hx : (s, t) ∈ K
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have : R < |s| := by
        by_contra h
        push_neg at h
        exact hx ⟨abs_le.1 h, Set.Ico_subset_Icc_self ht⟩
      exact (hR s t this).symm
  refine (memLp_congr_ae hae).1 ((memLp_indicator_iff_restrict hKm).2 ?_)
  haveI : IsFiniteMeasure (cylMeasure.restrict K) := by
    refine isFiniteMeasure_restrict.2 (ne_of_lt (lt_of_le_of_lt ?_ (hKc.measure_lt_top (μ := (volume : Measure (ℝ × ℝ))))))
    exact Measure.le_iff'.1 Measure.restrict_le_self K
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C (ae_restrict_of_forall_mem hKm hC)

lemma partialS_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialS u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialS, hev.fderiv_eq]

lemma partialT_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialT u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialT, hev.fderiv_eq]

lemma IsTestSection.continuous {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Continuous u :=
  hu.1.continuous

lemma IsTestSection.continuous_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialS u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.continuous_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialT u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.memLp {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : MemLp u p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish u hu.continuous R hR

lemma IsTestSection.memLp_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialS u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialS R fun s t hs => partialS_eq_zero R hR hs

lemma IsTestSection.memLp_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialT u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialT R fun s t hs => partialT_eq_zero R hR hs

lemma IsTestSection.sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u - v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.sub hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u + v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.add hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    IsTestSection (c • u) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  refine ⟨ContDiff.const_smul c hu.1, fun s t => by simp [hu.2.1], R₁, fun s t hs => ?_⟩
  simp [h₁ s t hs]

lemma isTestSection_zero : IsTestSection (0 : ℝ × ℝ → Vec n) :=
  ⟨contDiff_const, fun _ _ => rfl, 0, fun _ _ _ => rfl⟩

lemma partialS_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u + v) = partialS u + partialS v := by
  funext x
  simp only [partialS, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u + v) = partialT u + partialT v := by
  funext x
  simp only [partialT, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u - v) = partialS u - partialS v := by
  funext x
  simp only [partialS, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u - v) = partialT u - partialT v := by
  funext x
  simp only [partialT, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialS (c • u) = c • partialS u := by
  funext x
  simp only [partialS, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialT_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialT (c • u) = c • partialT u := by
  funext x
  simp only [partialT, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialS_zero : partialS (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialS]

lemma partialT_zero : partialT (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialT]

end

end CauchyRiemannIndex

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The triple `(u, ∂ₛu, ∂ₜu)` of a test section. -/
def testTriple {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Triple n p :=
  ((hu.memLp (p := p)).toLp u, (hu.memLp_partialS (p := p)).toLp _, (hu.memLp_partialT (p := p)).toLp _)

lemma testTriple_mem {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    testTriple (p := p) hu ∈ testTriples n p :=
  ⟨u, hu, (hu.memLp (p := p)).coeFn_toLp, (hu.memLp_partialS (p := p)).coeFn_toLp,
    (hu.memLp_partialT (p := p)).coeFn_toLp⟩

lemma span_testTriples_subset :
    (Submodule.span ℝ (testTriples n p) : Set (Triple n p)) ⊆ testTriples n p := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨0, isTestSection_zero, ?_, ?_, ?_⟩
    · exact Lp.coeFn_zero _ _ _
    · rw [partialS_zero]; exact Lp.coeFn_zero _ _ _
    · rw [partialT_zero]; exact Lp.coeFn_zero _ _ _
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, h1, h2, h3⟩ := hx
    obtain ⟨v, hv, k1, k2, k3⟩ := hy
    refine ⟨u + v, hu.add hv, ?_, ?_, ?_⟩
    · exact (Lp.coeFn_add x.1 y.1).trans (h1.add k1)
    · rw [partialS_add hu hv]; exact (Lp.coeFn_add x.2.1 y.2.1).trans (h2.add k2)
    · rw [partialT_add hu hv]; exact (Lp.coeFn_add x.2.2 y.2.2).trans (h3.add k3)
  | smul c x _ hx =>
    obtain ⟨u, hu, h1, h2, h3⟩ := hx
    refine ⟨c • u, hu.smul c, ?_, ?_, ?_⟩
    · exact (Lp.coeFn_smul c x.1).trans (h1.const_smul c)
    · rw [partialS_smul hu]; exact (Lp.coeFn_smul c x.2.1).trans (h2.const_smul c)
    · rw [partialT_smul hu]; exact (Lp.coeFn_smul c x.2.2).trans (h3.const_smul c)

lemma crApply_ae_crOp (S : ℝ × ℝ → Mat n) {w : Triple n p} {u : ℝ × ℝ → Vec n}
    (h1 : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u)
    (h2 : (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u)
    (h3 : (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u) :
    crApply S w =ᵐ[cylMeasure] crOp S u := by
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  simp only [crApply, crOp, e1, e2, e3]

lemma ofReal_norm_le_w1pNorm {w : Triple n p} {u : ℝ × ℝ → Vec n}
    (h1 : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u)
    (h2 : (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u)
    (h3 : (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u) :
    ENNReal.ofReal ‖w‖ ≤ w1pNorm p u := by
  have e1 : ENNReal.ofReal ‖w.1‖ = eLpNorm u p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h1]
  have e2 : ENNReal.ofReal ‖w.2.1‖ = eLpNorm (partialS u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h2]
  have e3 : ENNReal.ofReal ‖w.2.2‖ = eLpNorm (partialT u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h3]
  rw [Prod.norm_def, Prod.norm_def, ENNReal.ofReal_max, ENNReal.ofReal_max, e1, e2, e3]
  unfold w1pNorm
  refine max_le ?_ (max_le ?_ ?_)
  · exact le_add_right (le_add_right le_rfl)
  · exact le_add_right (le_add_left le_rfl)
  · exact le_add_left le_rfl

lemma eLpNorm_const_mul_norm_le (g : LpCyl n p) {c : ℝ} (hc : 0 ≤ c) :
    eLpNorm (fun x => c * ‖g x‖) p cylMeasure ≤ ENNReal.ofReal c * ENNReal.ofReal ‖g‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) p
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (norm_nonneg _))]

lemma eLpNorm_le_of_pointwise {F : ℝ × ℝ → Vec n} {w : Triple n p} {M MJ : ℝ}
    (hM : 0 ≤ M) (hMJ : 0 ≤ MJ)
    (hF : ∀ᵐ x ∂cylMeasure, ‖F x‖ ≤ 1 * ‖w.2.1 x‖ + MJ * ‖w.2.2 x‖ + M * ‖w.1 x‖) :
    eLpNorm F p cylMeasure ≤ ENNReal.ofReal (1 + MJ + M) * ENNReal.ofReal ‖w‖ := by
  have hp1 : 1 ≤ p := Fact.out
  have m1 : AEStronglyMeasurable (fun x => 1 * ‖w.2.1 x‖) cylMeasure :=
    (Lp.aestronglyMeasurable w.2.1).norm.const_mul 1
  have m2 : AEStronglyMeasurable (fun x => MJ * ‖w.2.2 x‖) cylMeasure :=
    (Lp.aestronglyMeasurable w.2.2).norm.const_mul MJ
  have m3 : AEStronglyMeasurable (fun x => M * ‖w.1 x‖) cylMeasure :=
    (Lp.aestronglyMeasurable w.1).norm.const_mul M
  have n1 : ‖w.2.1‖ ≤ ‖w‖ := (norm_fst_le w.2).trans (norm_snd_le w)
  have n2 : ‖w.2.2‖ ≤ ‖w‖ := (norm_snd_le w.2).trans (norm_snd_le w)
  have n3 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  calc eLpNorm F p cylMeasure
      ≤ eLpNorm (fun x => 1 * ‖w.2.1 x‖ + MJ * ‖w.2.2 x‖ + M * ‖w.1 x‖) p cylMeasure :=
        eLpNorm_mono_ae_real hF
    _ ≤ eLpNorm (fun x => 1 * ‖w.2.1 x‖) p cylMeasure + eLpNorm (fun x => MJ * ‖w.2.2 x‖) p cylMeasure
          + eLpNorm (fun x => M * ‖w.1 x‖) p cylMeasure := by
        refine (eLpNorm_add_le (m1.add m2) m3 hp1).trans ?_
        gcongr
        exact eLpNorm_add_le m1 m2 hp1
    _ ≤ ENNReal.ofReal 1 * ENNReal.ofReal ‖w.2.1‖ + ENNReal.ofReal MJ * ENNReal.ofReal ‖w.2.2‖
          + ENNReal.ofReal M * ENNReal.ofReal ‖w.1‖ := by
        gcongr
        · exact eLpNorm_const_mul_norm_le _ zero_le_one
        · exact eLpNorm_const_mul_norm_le _ hMJ
        · exact eLpNorm_const_mul_norm_le _ hM
    _ ≤ ENNReal.ofReal 1 * ENNReal.ofReal ‖w‖ + ENNReal.ofReal MJ * ENNReal.ofReal ‖w‖
          + ENNReal.ofReal M * ENNReal.ofReal ‖w‖ := by
        gcongr
    _ = ENNReal.ofReal (1 + MJ + M) * ENNReal.ofReal ‖w‖ := by
        rw [ENNReal.ofReal_add (by positivity) hM, ENNReal.ofReal_add zero_le_one hMJ]
        ring

lemma aestronglyMeasurable_crApply (Sinf : ℝ → Mat n) (hc : Continuous Sinf) (w : Triple n p) :
    AEStronglyMeasurable (crApply (fun x : ℝ × ℝ => Sinf x.2) w) cylMeasure := by
  have hJ : AEStronglyMeasurable (fun x => matCLM n (J₀ n) (w.2.2 x)) cylMeasure :=
    (matCLM n (J₀ n)).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w.2.2)
  have hS : AEStronglyMeasurable (fun x : ℝ × ℝ => matCLM n (Sinf x.2) (w.1 x)) cylMeasure :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (A : Vec n →L[ℝ] Vec n) (v : Vec n) => A v)
      (continuous_fst.clm_apply continuous_snd)
      ((continuous_matCLM.comp (hc.comp continuous_snd)).aestronglyMeasurable)
      (Lp.aestronglyMeasurable w.1)
  exact ((Lp.aestronglyMeasurable w.2.1).add hJ).add hS

lemma crApply_sub_ae (S : ℝ × ℝ → Mat n) (w w' : Triple n p) :
    crApply S (w - w') =ᵐ[cylMeasure] crApply S w - crApply S w' := by
  filter_upwards [Lp.coeFn_sub w.1 w'.1, Lp.coeFn_sub w.2.1 w'.2.1,
    Lp.coeFn_sub w.2.2 w'.2.2] with x e1 e2 e3
  change (⇑(w.2.1 - w'.2.1) x + _ + Matrix.toEuclideanLin (S x) (⇑(w.1 - w'.1) x)) = _
  change _ + Matrix.toEuclideanLin (J₀ n) (⇑(w.2.2 - w'.2.2) x) + _ = _
  rw [e1, e2, e3]
  simp only [crApply, Pi.sub_apply, map_sub]
  abel

end

end CauchyRiemannIndex

namespace CauchyRiemannIndex

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

/-- For `2 < p < ∞`, the first component of every `w ∈ W^{1,p}` has a continuous representative,
`1`-periodic in `t`; every such representative is bounded by `C ‖w‖` and tends to `0` as
`|s| → ∞`, uniformly in `t`. -/
theorem exists_continuous_representative_of_mem_W1p_aux (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p)
    (hp' : p ≠ ⊤) (n : ℕ) :
    ∃ C : ℝ, ∀ w ∈ W1p p n,
      (∃ g : ℝ × ℝ → Vec n, Continuous g ∧ (∀ s t, g (s, t + 1) = g (s, t)) ∧
        (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g) ∧
      ∀ g : ℝ × ℝ → Vec n, Continuous g → (∀ s t, g (s, t + 1) = g (s, t)) →
        (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g →
        (∀ x, ‖g x‖ ≤ C * ‖w‖) ∧ ∀ ε > 0, ∃ R : ℝ, ∀ s t, R < |s| → ‖g (s, t)‖ < ε := by
  obtain ⟨C0, hC0⟩ := enorm_le_w1pNorm_of_isTestSection (n := n) p hp hp'
  set C : ℝ := 3 * max C0 0 with hC
  have hCnn : 0 ≤ C := by positivity
  -- the bound on test triples
  have hT : ∀ (w : Triple n p) (u : ℝ × ℝ → Vec n), IsTestSection u →
      (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u →
      (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u →
      (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u → ∀ x, ‖u x‖ ≤ C * ‖w‖ := by
    intro w u hu h1 h2 h3 x
    have e1 : eLpNorm u p cylMeasure = ENNReal.ofReal ‖w.1‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h1]
    have e2 : eLpNorm (partialS u) p cylMeasure = ENNReal.ofReal ‖w.2.1‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h2]
    have e3 : eLpNorm (partialT u) p cylMeasure = ENNReal.ofReal ‖w.2.2‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h3]
    have n1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
    have n2 : ‖w.2.1‖ ≤ ‖w‖ := (norm_fst_le w.2).trans (norm_snd_le w)
    have n3 : ‖w.2.2‖ ≤ ‖w‖ := (norm_snd_le w.2).trans (norm_snd_le w)
    have hW : w1pNorm p u ≤ ENNReal.ofReal (3 * ‖w‖) := by
      unfold w1pNorm
      rw [e1, e2, e3, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
        ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have key : ‖u x‖ₑ ≤ ENNReal.ofReal C0 * ENNReal.ofReal (3 * ‖w‖) :=
      (hC0 u hu x).trans (by gcongr)
    have hmax : ENNReal.ofReal C0 ≤ ENNReal.ofReal (max C0 0) :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have key2 : ‖u x‖ₑ ≤ ENNReal.ofReal (C * ‖w‖) := by
      refine key.trans ((by gcongr : ENNReal.ofReal C0 * ENNReal.ofReal (3 * ‖w‖) ≤
        ENNReal.ofReal (max C0 0) * ENNReal.ofReal (3 * ‖w‖)).trans_eq ?_)
      rw [← ENNReal.ofReal_mul (le_max_right _ _), hC]; ring_nf
    rw [← ofReal_norm_eq_enorm] at key2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key2
  refine ⟨C, fun w hw => ?_⟩
  -- approximating test triples
  have hwcl : w ∈ closure (Submodule.span ℝ (testTriples n p) : Set (Triple n p)) := by
    have : w ∈ (W1p p n : Set (Triple n p)) := hw
    rwa [W1p, Submodule.topologicalClosure_coe] at this
  obtain ⟨wk, hwk, hlim⟩ := mem_closure_iff_seq_limit.1 hwcl
  have hwkT : ∀ k, wk k ∈ testTriples n p := fun k => span_testTriples_subset (hwk k)
  choose u hu h1 h2 h3 using hwkT
  have hdiff : ∀ k l x, ‖u k x - u l x‖ ≤ C * ‖wk k - wk l‖ := by
    intro k l x
    have := hT (wk k - wk l) (u k - u l) ((hu k).sub (hu l))
      ((Lp.coeFn_sub _ _).trans ((h1 k).sub (h1 l)))
      (by rw [partialS_sub (hu k) (hu l)]; exact (Lp.coeFn_sub _ _).trans ((h2 k).sub (h2 l)))
      (by rw [partialT_sub (hu k) (hu l)]; exact (Lp.coeFn_sub _ _).trans ((h3 k).sub (h3 l))) x
    simpa using this
  set U : ℕ → BoundedContinuousFunction (ℝ × ℝ) (Vec n) := fun k =>
    BoundedContinuousFunction.ofNormedAddCommGroup (u k) (hu k).continuous (C * ‖wk k‖)
      (hT (wk k) (u k) (hu k) (h1 k) (h2 k) (h3 k)) with hUdef
  have hUapp : ∀ k x, U k x = u k x := fun _ _ => rfl
  have hUdist : ∀ k l, dist (U k) (U l) ≤ C * ‖wk k - wk l‖ := by
    intro k l
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_
    rw [hUapp, hUapp, dist_eq_norm]; exact hdiff k l x
  have hUc : CauchySeq U := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq (ε / (C + 1)) (by positivity)
    refine ⟨N, fun k hk l hl => (hUdist k l).trans_lt ?_⟩
    have := hN k hk l hl
    rw [dist_eq_norm] at this
    calc C * ‖wk k - wk l‖ ≤ (C + 1) * ‖wk k - wk l‖ := by gcongr; linarith
      _ < (C + 1) * (ε / (C + 1)) := by gcongr
      _ = ε := by field_simp
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hUc
  have hpt : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (G x)) := fun x =>
    ((continuous_eval_const x).tendsto G).comp hG
  have hGper : ∀ s t, G (s, t + 1) = G (s, t) := by
    intro s t
    refine tendsto_nhds_unique (hpt (s, t + 1)) ?_
    simp_rw [(hu _).2.1 s t]; exact hpt (s, t)
  -- the a.e. identification
  have hGae : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] G := by
    have hl1 : Tendsto (fun k => (wk k).1) atTop (𝓝 w.1) :=
      (continuous_fst.tendsto w).comp hlim
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hl1
    have hm := tendstoInMeasure_of_tendsto_eLpNorm (p := p) (by positivity)
      (fun k => (Lp.aestronglyMeasurable (wk k).1)) (Lp.aestronglyMeasurable w.1) hl1
    obtain ⟨ns, hns_mono, hns⟩ := hm.exists_seq_tendsto_ae
    have hall : ∀ᵐ x ∂cylMeasure, ∀ k, ((wk k).1 : ℝ × ℝ → Vec n) x = u k x :=
      ae_all_iff.2 h1
    filter_upwards [hns, hall] with x hx hxa
    refine tendsto_nhds_unique hx ?_
    simp_rw [hxa]
    exact (hpt x).comp hns_mono.tendsto_atTop
  refine ⟨⟨G, G.continuous, hGper, hGae⟩, fun g hg hgp hgae => ?_⟩
  have hgG : g = G := eq_of_continuous_periodic_ae_eq hg G.continuous hgp hGper (hgae.symm.trans hGae)
  subst hgG
  refine ⟨fun x => ?_, fun ε hε => ?_⟩
  · have hb : ∀ k, ‖u k x‖ ≤ C * ‖wk k‖ := fun k => hT (wk k) (u k) (hu k) (h1 k) (h2 k) (h3 k) x
    exact le_of_tendsto_of_tendsto' (hpt x).norm
      (((continuous_norm.tendsto w).comp hlim).const_mul C) hb
  · obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hG (ε / 2) (by positivity)
    set k := N
    have hk := hN k le_rfl
    obtain ⟨R, hR⟩ := (hu k).2.2
    refine ⟨R, fun s t hs => ?_⟩
    have h0 : U k (s, t) = 0 := by rw [hUapp]; exact hR s t hs
    have := (BoundedContinuousFunction.dist_coe_le_dist (f := U k) (g := G) (s, t)).trans_lt hk
    rw [h0, dist_comm, dist_zero_right] at this
    linarith

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal NNReal

theorem solution (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p)
    (hp' : p ≠ ⊤) (n : ℕ) :
    ∃ C : ℝ, ∀ w ∈ W1p p n,
      (∃ g : ℝ × ℝ → Vec n, Continuous g ∧ (∀ s t, g (s, t + 1) = g (s, t)) ∧
        (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g) ∧
      ∀ g : ℝ × ℝ → Vec n, Continuous g → (∀ s t, g (s, t + 1) = g (s, t)) →
        (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g →
        (∀ x, ‖g x‖ ≤ C * ‖w‖) ∧ ∀ ε > 0, ∃ R : ℝ, ∀ s t, R < |s| → ‖g (s, t)‖ < ε :=
  exists_continuous_representative_of_mem_W1p_aux p hp hp' n
