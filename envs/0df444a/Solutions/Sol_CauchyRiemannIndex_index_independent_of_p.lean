-- Prove2me | solution 1 for CauchyRiemannIndex.index_independent_of_p
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T11:27:52.095984+00:00
-- url     : https://prove2.me/submissions/0ea80a27-3b16-493e-b368-540c36deaf52

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Theorems.Thm_CauchyRiemannIndex_global_estimate
import Theorems.Thm_CauchyRiemannIndex_compact_restriction
import Theorems.Thm_CauchyRiemannIndex_finiteDimensional_ker_isClosed_range_of_estimate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Instances.Matrix
import Theorems.Thm_CauchyRiemannIndex_finrank_quotient_eq_finrank_annihilator
import Theorems.Thm_CauchyRiemannIndex_memW1p_of_weak_solution
import Theorems.Thm_CauchyRiemannIndex_semiFredholm
import Theorems.Thm_CauchyRiemannIndex_crOp_formalAdjoint
import Theorems.Thm_CauchyRiemannIndex_eLpNorm_two_mul_le_w1pNorm
import Theorems.Thm_CauchyRiemannIndex_memLp_of_le_of_le
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Comp
import Theorems.Thm_CauchyRiemannIndex_cokernel_eq_kernel_adjoint
import Theorems.Thm_CauchyRiemannIndex_conj_isAsymptoticTo
import Theorems.Thm_CauchyRiemannIndex_conj_loop_isSymLoop_isNondegenerate

-- ===== Scratch/CR411Bridge.lean =====
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

-- ===== Scratch/CR411Core.lean =====
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

-- ===== Scratch/CRSF.lean =====
/-!
# Wendl, Corollary 4.14 (`k = 1`): `D_S` is semi-Fredholm

`D_S` and the restriction `K : W^{1,p} → L^p([-R, R] × S¹)` are bounded operators on the Banach
space `W^{1,p}`. The global estimate (Lemma 4.13) extends from test sections to `W^{1,p}` by
density, `K` is compact by the Rellich milestone, and Lemma 4.12 gives a finite-dimensional
kernel and a closed range.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma crs_per {β : Type*} {F : ℝ × ℝ → β} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (s t : ℝ) :
    F (s, Int.fract t) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hF s t
  have := hp.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at this
  exact this

lemma crs_matbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ D : Mat n, (∀ i j, |D i j| ≤ 1) → ‖matCLM n D‖ ≤ B := by
  have hK : IsCompact {D : Mat n | ∀ i j, D i j ∈ Set.Icc (-1 : ℝ) 1} := by
    have e : {D : Mat n | ∀ i j, D i j ∈ Set.Icc (-1 : ℝ) 1} =
        Set.univ.pi (fun _ => Set.univ.pi fun _ => Set.Icc (-1 : ℝ) 1) := by
      ext D
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn continuous_matCLM.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun D hD =>
    (hB D fun i j => Set.mem_Icc.2 (abs_le.1 (hD i j))).trans (le_max_left _ _)⟩

/-- An asymptotic coefficient is bounded. -/
lemma crs_Sbound {S : ℝ × ℝ → Mat n} {Splus Sminus : ℝ → Mat n} (hSp : IsSymLoop Splus)
    (hSm : IsSymLoop Sminus) (hS : IsAsymptoticTo S Splus Sminus) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖ := by
  obtain ⟨Mp, hMp0, hMp⟩ := exists_bound_loop Splus hSp.1 hSp.2.1
  obtain ⟨Mm, hMm0, hMm⟩ := exists_bound_loop Sminus hSm.1 hSm.2.1
  obtain ⟨B, hB0, hB⟩ := crs_matbound (n := n)
  obtain ⟨R, hR⟩ := hS.2.2 1 one_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      (continuous_matCLM.comp hS.1).continuousOn
  refine ⟨max C 0 + B + Mp + Mm, by positivity, fun x v => ?_⟩
  have hv := norm_nonneg v
  have hsplit : ∀ T : Mat n, Matrix.toEuclideanLin (S x) v =
      matCLM n (S x - T) v + Matrix.toEuclideanLin T v := by
    intro T
    rw [matCLM_apply, ← LinearMap.add_apply, ← map_add, sub_add_cancel]
  by_cases h1 : R ≤ x.1
  · rw [hsplit (Splus x.2)]
    have hD : ‖matCLM n (S x - Splus x.2)‖ ≤ B :=
      hB _ fun i j => by simpa using (hR x.1 x.2 i j).1 h1
    calc ‖matCLM n (S x - Splus x.2) v + Matrix.toEuclideanLin (Splus x.2) v‖
        ≤ ‖matCLM n (S x - Splus x.2)‖ * ‖v‖ + Mp * ‖v‖ :=
          (norm_add_le _ _).trans (add_le_add ((matCLM n _).le_opNorm v) (hMp _ v))
      _ ≤ B * ‖v‖ + Mp * ‖v‖ := by gcongr
      _ ≤ (max C 0 + B + Mp + Mm) * ‖v‖ := by
          nlinarith [le_max_right C 0]
  by_cases h2 : x.1 ≤ -R
  · rw [hsplit (Sminus x.2)]
    have hD : ‖matCLM n (S x - Sminus x.2)‖ ≤ B :=
      hB _ fun i j => by simpa using (hR x.1 x.2 i j).2 h2
    calc ‖matCLM n (S x - Sminus x.2) v + Matrix.toEuclideanLin (Sminus x.2) v‖
        ≤ ‖matCLM n (S x - Sminus x.2)‖ * ‖v‖ + Mm * ‖v‖ :=
          (norm_add_le _ _).trans (add_le_add ((matCLM n _).le_opNorm v) (hMm _ v))
      _ ≤ B * ‖v‖ + Mm * ‖v‖ := by gcongr
      _ ≤ (max C 0 + B + Mp + Mm) * ‖v‖ := by
          nlinarith [le_max_right C 0]
  push_neg at h1 h2
  have hx : (x.1, Int.fract x.2) ∈ Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1 := by
    refine Set.mk_mem_prod ⟨?_, ?_⟩ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    · have := le_abs_self R; linarith
    · have := le_abs_self R; linarith
  have hCx := hC _ hx
  have e : S (x.1, Int.fract x.2) = S x := crs_per hS.2.1 x.1 x.2
  simp only [Function.comp, e] at hCx
  rw [← matCLM_apply]
  calc ‖matCLM n (S x) v‖ ≤ ‖matCLM n (S x)‖ * ‖v‖ := (matCLM n _).le_opNorm v
    _ ≤ max C 0 * ‖v‖ := by gcongr; exact hCx.trans (le_max_left _ _)
    _ ≤ (max C 0 + B + Mp + Mm) * ‖v‖ := by nlinarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma crs_aesm (S : ℝ × ℝ → Mat n) (hc : Continuous S) (w : Triple n p) :
    AEStronglyMeasurable (crApply S w) cylMeasure := by
  have hJ : AEStronglyMeasurable (fun x => matCLM n (J₀ n) (w.2.2 x)) cylMeasure :=
    (matCLM n (J₀ n)).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w.2.2)
  have hS : AEStronglyMeasurable (fun x : ℝ × ℝ => matCLM n (S x) (w.1 x)) cylMeasure :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (A : Vec n →L[ℝ] Vec n) (v : Vec n) => A v)
      (continuous_fst.clm_apply continuous_snd)
      ((continuous_matCLM.comp hc).aestronglyMeasurable)
      (Lp.aestronglyMeasurable w.1)
  exact ((Lp.aestronglyMeasurable w.2.1).add hJ).add hS

/-- The operator-norm constant of `D_S` on triples. -/
def crsC (S : ℝ × ℝ → Mat n)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖) : ℝ :=
  1 + ‖matCLM n (J₀ n)‖ + hb.choose

lemma crsC_nonneg (S : ℝ × ℝ → Mat n)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖) :
    0 ≤ crsC S hb := by
  unfold crsC
  have := hb.choose_spec.1
  positivity

lemma crs_eLpNorm_le (S : ℝ × ℝ → Mat n)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) :
    eLpNorm (crApply S w) p cylMeasure ≤ ENNReal.ofReal (crsC S hb) * ENNReal.ofReal ‖w‖ := by
  unfold crsC
  refine eLpNorm_le_of_pointwise hb.choose_spec.1 (norm_nonneg _) (Eventually.of_forall fun x => ?_)
  unfold crApply
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [one_mul]
  · rw [← matCLM_apply]; exact (matCLM n (J₀ n)).le_opNorm _
  · exact hb.choose_spec.2 x _

lemma crs_memLp (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) : MemLp (crApply S w) p cylMeasure :=
  ⟨crs_aesm S hc w, (crs_eLpNorm_le S hb w).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)⟩

lemma crs_add_ae (S : ℝ × ℝ → Mat n) (w w' : Triple n p) :
    crApply S (w + w') =ᵐ[cylMeasure] crApply S w + crApply S w' := by
  filter_upwards [Lp.coeFn_add w.1 w'.1, Lp.coeFn_add w.2.1 w'.2.1,
    Lp.coeFn_add w.2.2 w'.2.2] with x e1 e2 e3
  change (⇑(w.2.1 + w'.2.1) x + _ + Matrix.toEuclideanLin (S x) (⇑(w.1 + w'.1) x)) = _
  change _ + Matrix.toEuclideanLin (J₀ n) (⇑(w.2.2 + w'.2.2) x) + _ = _
  rw [e1, e2, e3]
  simp only [crApply, Pi.add_apply, map_add]
  abel

lemma crs_smul_ae (S : ℝ × ℝ → Mat n) (c : ℝ) (w : Triple n p) :
    crApply S (c • w) =ᵐ[cylMeasure] c • crApply S w := by
  filter_upwards [Lp.coeFn_smul c w.1, Lp.coeFn_smul c w.2.1,
    Lp.coeFn_smul c w.2.2] with x e1 e2 e3
  change (⇑(c • w.2.1) x + _ + Matrix.toEuclideanLin (S x) (⇑(c • w.1) x)) = _
  change _ + Matrix.toEuclideanLin (J₀ n) (⇑(c • w.2.2) x) + _ = _
  rw [e1, e2, e3]
  simp only [crApply, Pi.smul_apply, map_smul, smul_add]

/-- `D_S` as a bounded operator `L^p × L^p × L^p → L^p`. -/
def crsT (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖) :
    Triple n p →L[ℝ] LpCyl n p :=
  LinearMap.mkContinuous
    { toFun := fun w => (crs_memLp S hc hb w).toLp _
      map_add' := fun w w' => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (crs_memLp S hc hb (w + w')),
          Lp.coeFn_add ((crs_memLp S hc hb w).toLp _) ((crs_memLp S hc hb w').toLp _),
          MemLp.coeFn_toLp (crs_memLp S hc hb w), MemLp.coeFn_toLp (crs_memLp S hc hb w'),
          crs_add_ae S w w'] with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
      map_smul' := fun c w => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (crs_memLp S hc hb (c • w)),
          Lp.coeFn_smul c ((crs_memLp S hc hb w).toLp _),
          MemLp.coeFn_toLp (crs_memLp S hc hb w), crs_smul_ae S c w] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply] }
    (crsC S hb) (fun w => by
      change ‖(crs_memLp S hc hb w).toLp _‖ ≤ _
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (crsC_nonneg S hb) (norm_nonneg _)) ?_
      rw [ENNReal.ofReal_mul (crsC_nonneg S hb)]
      exact crs_eLpNorm_le S hb w)

lemma crsT_ae (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) : (crsT S hc hb w : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] crApply S w :=
  MemLp.coeFn_toLp (crs_memLp S hc hb w)

variable (n p) in
/-- The strip `[-R, R] × S¹` (as a subset of the fundamental domain). -/
abbrev crsμ (R : ℝ) : Measure (ℝ × ℝ) := cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)

variable (n p) in
/-- `(u, v, w) ↦ u|_{[-R, R] × S¹}`. -/
def crsK (R : ℝ) : Triple n p →L[ℝ] Lp (Vec n) p (crsμ R) :=
  (LpToLpRestrictCLM (ℝ × ℝ) (Vec n) ℝ cylMeasure p (Set.Icc (-R) R ×ˢ Set.univ)).comp
    (ContinuousLinearMap.fst ℝ (LpCyl n p) (LpCyl n p × LpCyl n p))

lemma crsK_ae (R : ℝ) (w : Triple n p) :
    (crsK n p R w : ℝ × ℝ → Vec n) =ᵐ[crsμ R] w.1 :=
  LpToLpRestrictCLM_coeFn ℝ _ w.1

/-- `w1pNorm u ≤ 3 ‖(u, ∂ₛu, ∂ₜu)‖`. -/
lemma crs_w1p_le {w : Triple n p} {u : ℝ × ℝ → Vec n}
    (h1 : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u)
    (h2 : (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u)
    (h3 : (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u) :
    w1pNorm p u ≤ ENNReal.ofReal (3 * ‖w‖) := by
  have e1 : ENNReal.ofReal ‖w.1‖ = eLpNorm u p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h1]
  have e2 : ENNReal.ofReal ‖w.2.1‖ = eLpNorm (partialS u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h2]
  have e3 : ENNReal.ofReal ‖w.2.2‖ = eLpNorm (partialT u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h3]
  have n1 : ‖w.2.1‖ ≤ ‖w‖ := (norm_fst_le w.2).trans (norm_snd_le w)
  have n2 : ‖w.2.2‖ ≤ ‖w‖ := (norm_snd_le w.2).trans (norm_snd_le w)
  have n3 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  unfold w1pNorm
  rw [← e1, ← e2, ← e3, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The global estimate on the closed span of test triples. -/
lemma crs_estimate (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (R : ℝ) (c : ℝ≥0)
    (hest : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure + c * eLpNorm u p (crsμ R)) :
    ∀ w ∈ W1p p n, ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖ := by
  have htest : ∀ w ∈ testTriples n p, ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖ := by
    rintro w ⟨u, hu, h1, h2, h3⟩
    have eT : ENNReal.ofReal ‖crsT S hc hb w‖ = eLpNorm (crOp S u) p cylMeasure := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
        eLpNorm_congr_ae ((crsT_ae S hc hb w).trans (crApply_ae_crOp S h1 h2 h3))]
    have eK : ENNReal.ofReal ‖crsK n p R w‖ = eLpNorm u p (crsμ R) := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
        eLpNorm_congr_ae ((crsK_ae R w).trans (ae_restrict_of_ae h1))]
    have h := (ofReal_norm_le_w1pNorm h1 h2 h3).trans (hest u hu)
    have h' : ENNReal.ofReal ‖w‖ ≤
        ENNReal.ofReal ((c : ℝ) * ‖crsT S hc hb w‖ + (c : ℝ) * ‖crsK n p R w‖) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul c.coe_nonneg,
        ENNReal.ofReal_mul c.coe_nonneg, eT, eK, ENNReal.ofReal_coe_nnreal]
      exact h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h'
  have hcl : IsClosed {w : Triple n p | ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖} :=
    isClosed_le continuous_norm
      ((continuous_const.mul (crsT S hc hb).continuous.norm).add
        (continuous_const.mul (crsK n p R).continuous.norm))
  intro w hw
  have hsub : (W1p p n : Set (Triple n p)) ⊆
      {w : Triple n p | ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖} := by
    unfold W1p
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal (fun w hw => htest w (span_testTriples_subset hw)) hcl
  exact hsub hw

end

end CauchyRiemannIndex

-- ===== Scratch/CRCylCalc.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma cylMeasure_eq_prod :
    cylMeasure = (volume : Measure ℝ).prod (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  rw [cylMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

lemma fderiv_eq_zero_of_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ × ℝ → E} (R : ℝ) (hR : ∀ s t, R < |s| → φ (s, t) = 0) {s t : ℝ} (hs : R < |s|) :
    fderiv ℝ φ (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : φ =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  rw [hev.fderiv_eq]; simp

lemma hasCompactSupport_of_vanish {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (R : ℝ)
    (hR : ∀ s, R < |s| → f s = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs =>
    hR s (not_le.1 fun h => hs (abs_le.1 h))

/-- `∫ ∂ₛφ = 0` over the cylinder for a `C¹` function vanishing for large `|s|`. -/
lemma integral_fderiv_s_eq_zero (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (R : ℝ)
    (hR : ∀ s t, R < |s| → φ (s, t) = 0) :
    ∫ x, fderiv ℝ φ x (1, 0) ∂cylMeasure = 0 := by
  have hc : Continuous fun x => fderiv ℝ φ x (1, 0) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hI : Integrable (fun x => fderiv ℝ φ x (1, 0)) cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish _ hc R fun s t hs => by simp [fderiv_eq_zero_of_vanish R hR hs]
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod_symm _ hI]
  have h : ∀ t : ℝ, ∫ s, fderiv ℝ φ (s, t) (1, 0) = 0 := by
    intro t
    have hd : ∀ s, HasDerivAt (fun s => φ (s, t)) (fderiv ℝ φ (s, t) (1, 0)) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ)) s :=
        (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
      exact ((hφ.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt s h1
    refine integral_eq_zero_of_hasDerivAt_of_integrable hd ?_ ?_
    · exact (hc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish R fun s hs => by
          simp [fderiv_eq_zero_of_vanish R hR hs])
    · exact (hφ.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish R fun s hs => hR s t hs)
  simp [h]

/-- `∫ ∂ₜφ = 0` over the cylinder for a `C¹` function, `1`-periodic in `t`, vanishing for large
`|s|`. -/
lemma integral_fderiv_t_eq_zero (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hper : ∀ s t, φ (s, t + 1) = φ (s, t)) (R : ℝ) (hR : ∀ s t, R < |s| → φ (s, t) = 0) :
    ∫ x, fderiv ℝ φ x (0, 1) ∂cylMeasure = 0 := by
  have hc : Continuous fun x => fderiv ℝ φ x (0, 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hI : Integrable (fun x => fderiv ℝ φ x (0, 1)) cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish _ hc R fun s t hs => by simp [fderiv_eq_zero_of_vanish R hR hs]
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod _ hI]
  have h : ∀ s : ℝ, ∫ t in Set.Ico (0 : ℝ) 1, fderiv ℝ φ (s, t) (0, 1) = 0 := by
    intro s
    have hd : ∀ t, HasDerivAt (fun t => φ (s, t)) (fderiv ℝ φ (s, t) (0, 1)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) t :=
        (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
      exact ((hφ.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt t h1
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        ((hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
    have := hper s 0
    simp only [zero_add] at this
    rw [this, sub_self]
  simp [h]

lemma inner_toEuclideanLin (A : Mat n) (x y : Vec n) :
    inner ℝ (Matrix.toEuclideanLin A x) y = inner ℝ x (Matrix.toEuclideanLin Aᵀ y) := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [h, LinearMap.adjoint_inner_right]

lemma fderiv_matCLM_comp {v : ℝ × ℝ → Vec n} (A : Mat n) {x : ℝ × ℝ}
    (hv : DifferentiableAt ℝ v x) (h : ℝ × ℝ) :
    fderiv ℝ (fun y => Matrix.toEuclideanLin A (v y)) x h =
      Matrix.toEuclideanLin A (fderiv ℝ v x h) := by
  have : (fun y => Matrix.toEuclideanLin A (v y)) = (matCLM n A) ∘ v := rfl
  rw [this, fderiv_comp x (matCLM n A).differentiableAt hv, ContinuousLinearMap.fderiv]
  rfl

end

end CauchyRiemannIndex

-- ===== Scratch/CokerPair.lean =====
namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

noncomputable section

section Pairing

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

lemma cka_integrable (f : Lp E p μ) (g : Lp E q μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  have h := MemLp.of_bilin (r := 1) (fun a b => inner ℝ a b) 1 (Lp.memLp f) (Lp.memLp g)
    ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g))
    (Filter.Eventually.of_forall fun x => by
      rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
      exact norm_inner_le_norm _ _)
  exact memLp_one_iff_integrable.1 h

/-- The pairing `∫ ⟨f, g⟩` as a bilinear map. -/
def ckaPair : Lp E p μ →ₗ[ℝ] Lp E q μ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => ∫ x, inner ℝ (f x) (g x) ∂μ)
    (fun f f' g => by
      rw [← integral_add (cka_integrable f g) (cka_integrable f' g)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add f f'] with x hx
      rw [hx, Pi.add_apply, inner_add_left])
    (fun c f g => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c f] with x hx
      rw [hx, Pi.smul_apply, real_inner_smul_left])
    (fun f g g' => by
      rw [← integral_add (cka_integrable f g) (cka_integrable f g')]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add g g'] with x hx
      rw [hx, Pi.add_apply, inner_add_right])
    (fun c f g => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c g] with x hx
      rw [hx, Pi.smul_apply, real_inner_smul_right])

lemma ckaPair_apply (f : Lp E p μ) (g : Lp E q μ) :
    ckaPair f g = ∫ x, inner ℝ (f x) (g x) ∂μ := rfl

omit [p.HolderConjugate q] in
/-- An `L^q` function orthogonal to all of `L^p` vanishes. -/
lemma cka_sep [SigmaFinite μ] [CompleteSpace E] (hp' : p ≠ ⊤) (hq' : q ≠ ⊤) (g : Lp E q μ)
    (hg : ∀ f : Lp E p μ, ∫ x, inner ℝ (f x) (g x) ∂μ = 0) : g = 0 := by
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  have hint : ∀ s, MeasurableSet s → μ s < ⊤ → IntegrableOn (g : α → E) s μ := by
    intro s hs hμs
    haveI : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hμs⟩
    exact ((Lp.memLp g).restrict s).integrable Fact.out
  have hae := ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (f := (g : α → E)) hint
    (fun s hs hμs => by
      rw [← inner_self_eq_zero (𝕜 := ℝ)]
      set e := ∫ x in s, (g : α → E) x ∂μ
      rw [← hg (indicatorConstLp p hs hμs.ne e)]
      calc inner ℝ e e = ∫ x in s, inner ℝ e ((g : α → E) x) ∂μ := by
            have := (innerSL ℝ e).integral_comp_comm (hint s hs hμs)
            simp only [innerSL_apply_apply] at this
            exact this.symm
        _ = ∫ x, s.indicator (fun x => inner ℝ e ((g : α → E) x)) x ∂μ :=
            (integral_indicator hs).symm
        _ = _ := by
            refine integral_congr_ae ?_
            filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs.ne) (c := e)]
              with x hx
            rw [hx]
            by_cases hxs : x ∈ s
            · simp [Set.indicator_of_mem hxs]
            · simp [Set.indicator_of_notMem hxs])
  exact (Lp.eq_zero_iff_ae_eq_zero).2 hae


/-- Hölder's inequality for the pairing. -/
lemma cka_bound (f : Lp E p μ) (g : Lp E q μ) : ‖ckaPair f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [ckaPair_apply]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hb := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := p) (q := q) (r := 1) (Lp.aestronglyMeasurable f)
    (Lp.aestronglyMeasurable g) (fun a b => inner ℝ a b) 1
    (Filter.Eventually.of_forall fun x => by
      rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
      exact norm_inner_le_norm _ _)
  simp only [ENNReal.coe_one, one_mul] at hb
  have hi := cka_integrable f g
  rw [integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable, ← eLpNorm_one_eq_lintegral_enorm,
    Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)) hb

/-- The pairing as a continuous bilinear map. -/
def ckaPairL : Lp E p μ →L[ℝ] Lp E q μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ ckaPair 1 fun f g => by
    rw [one_mul, Real.norm_eq_abs, ← Real.norm_eq_abs]; exact cka_bound f g

lemma ckaPairL_apply (f : Lp E p μ) (g : Lp E q μ) :
    ckaPairL f g = ∫ x, inner ℝ (f x) (g x) ∂μ := rfl

end Pairing

end

end CauchyRiemannIndex

-- ===== Scratch/CokerMat.lean =====
/-!
# Complex conjugation and the conjugated coefficient `S̄ = -C Sᵀ C`
-/

namespace CauchyRiemannIndex

open Matrix

noncomputable section

variable {n : ℕ}

/-- `A ↦ -C Aᵀ C`. -/
def cBar (A : Mat n) : Mat n := -(conjMat n * Aᵀ * conjMat n)

/-- The diagonal of `C`. -/
def cDiag (n : ℕ) : Fin n ⊕ Fin n → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

lemma cDiag_mul_self (i : Fin n ⊕ Fin n) : cDiag n i * cDiag n i = 1 := by
  cases i <;> simp [cDiag]

lemma abs_cDiag (i : Fin n ⊕ Fin n) : |cDiag n i| = 1 := by
  cases i <;> simp [cDiag]

lemma conjMat_eq_diagonal : conjMat n = diagonal (cDiag n) := by
  unfold conjMat cDiag
  rw [← fromBlocks_diagonal, diagonal_one]
  congr 1
  rw [← diagonal_one, ← diagonal_neg]

lemma conjMat_mul_self : conjMat n * conjMat n = 1 := by
  rw [conjMat_eq_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact cDiag_mul_self i

lemma conjMat_transpose : (conjMat n)ᵀ = conjMat n := by
  rw [conjMat_eq_diagonal, diagonal_transpose]

lemma conjMat_mul_J : conjMat n * J₀ n = -(J₀ n * conjMat n) := by
  simp [conjMat, J₀, Matrix.J, fromBlocks_multiply, fromBlocks_neg]

lemma conj_entry (A : Mat n) (i j : Fin n ⊕ Fin n) :
    (conjMat n * A * conjMat n) i j = cDiag n i * A i j * cDiag n j := by
  rw [conjMat_eq_diagonal, mul_diagonal, diagonal_mul]

lemma cBar_entry (A : Mat n) (i j : Fin n ⊕ Fin n) :
    cBar A i j = -(cDiag n i * A j i * cDiag n j) := by
  rw [cBar, neg_apply, conj_entry, transpose_apply]

lemma abs_cBar_sub (A B : Mat n) (i j : Fin n ⊕ Fin n) :
    |cBar A i j - cBar B i j| = |A j i - B j i| := by
  rw [cBar_entry, cBar_entry, show -(cDiag n i * A j i * cDiag n j) - -(cDiag n i * B j i * cDiag n j)
    = -(cDiag n i * (A j i - B j i) * cDiag n j) by ring, abs_neg, abs_mul, abs_mul, abs_cDiag,
    abs_cDiag, one_mul, mul_one]

lemma cBar_transpose (A : Mat n) : (cBar A)ᵀ = -(conjMat n * A * conjMat n) := by
  rw [cBar, transpose_neg, transpose_mul, transpose_mul, transpose_transpose, conjMat_transpose,
    mul_assoc]

lemma continuous_cBar : Continuous (cBar : Mat n → Mat n) :=
  ((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const).neg

lemma isSymLoop_cBar {T : ℝ → Mat n} (h : IsSymLoop T) : IsSymLoop (fun t => cBar (T t)) := by
  refine ⟨continuous_cBar.comp h.1, fun t => by simp only [h.2.1 t], fun t => ?_⟩
  show (cBar (T t))ᵀ = cBar (T t)
  rw [cBar_transpose, cBar, (h.2.2 t).eq]

lemma isAsymptoticTo_cBar {S : ℝ × ℝ → Mat n} {Splus Sminus : ℝ → Mat n}
    (h : IsAsymptoticTo S Splus Sminus) :
    IsAsymptoticTo (fun x => cBar (S x)) (fun t => cBar (Splus t)) (fun t => cBar (Sminus t)) := by
  refine ⟨continuous_cBar.comp h.1, fun s t => by simp only [h.2.1 s t], fun ε hε => ?_⟩
  obtain ⟨R, hR⟩ := h.2.2 ε hε
  refine ⟨R, fun s t i j => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rw [abs_cBar_sub]; exact (hR s t j i).1 hs
  · rw [abs_cBar_sub]; exact (hR s t j i).2 hs

lemma isNondegenerate_cBar {T : ℝ → Mat n} (hT : IsSymLoop T) (h : IsNondegenerate T) :
    IsNondegenerate (fun t => cBar (T t)) := by
  intro Ψ hΨ
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  set C := conjMat n
  have hCC : C * C = 1 := conjMat_mul_self
  have hfund : IsFundamentalSolution T (fun t => C * Ψ t * C) := by
    refine ⟨by simp [hΨ.1, hCC], fun t => ?_⟩
    have hsym : (T t)ᵀ = T t := (hT.2.2 t).eq
    have hCJ : C * J₀ n = -(J₀ n * C) := conjMat_mul_J
    have hd := ((hΨ.2 t).const_mul C).mul_const C
    have hb : cBar (T t) = -(C * T t * C) := by
      unfold cBar; rw [hsym]
    refine hd.congr_deriv ?_
    simp only []
    rw [hb]
    calc C * (J₀ n * -(C * T t * C) * Ψ t) * C = -(C * J₀ n * C * T t * C * Ψ t * C) := by
          noncomm_ring
      _ = J₀ n * (C * C) * T t * (C * Ψ t * C) := by
          rw [hCJ]; noncomm_ring
      _ = J₀ n * T t * (C * Ψ t * C) := by rw [hCC, mul_one]
  have hdet := h _ hfund
  intro h0
  apply hdet
  have : (1 : Mat n) - C * Ψ 1 * C = C * (1 - Ψ 1) * C := by
    rw [mul_sub, sub_mul, mul_one, hCC]
  rw [this, det_mul, det_mul, h0, mul_zero, zero_mul]

end

end CauchyRiemannIndex

-- ===== Scratch/CokerP.lean =====
/-!
# Wendl, Lemma 4.17 / Proposition 4.18 / Theorem 4.20 on the cylinder

The `L^q` annihilator of `im D_S` is `C · ker D_{S̄}`, and the codimension of the closed range
equals the dimension of that annihilator.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### Pointwise algebra -/

lemma ckp_toEL_mul (A B : Mat n) (x : Vec n) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) = Matrix.toEuclideanLin (A * B) x := by
  simp [toEuclideanLin_apply, mulVec_mulVec]

lemma ckp_toEL_neg (A : Mat n) (x : Vec n) :
    Matrix.toEuclideanLin (-A) x = -Matrix.toEuclideanLin A x := by
  rw [map_neg, LinearMap.neg_apply]

lemma ckp_inner_conj (x y : Vec n) :
    inner ℝ (Matrix.toEuclideanLin (conjMat n) x) y =
      inner ℝ x (Matrix.toEuclideanLin (conjMat n) y) := by
  rw [inner_toEuclideanLin, conjMat_transpose]

lemma ckp_conj_conj (x : Vec n) :
    Matrix.toEuclideanLin (conjMat n) (Matrix.toEuclideanLin (conjMat n) x) = x := by
  rw [ckp_toEL_mul, conjMat_mul_self]
  simp [toEuclideanLin_apply]

/-- `C (-a + J₀ b + S̄ᵀ c) = -(C a + J₀ C b + A C c)`. -/
lemma ckp_key1 (A : Mat n) (a b c : Vec n) :
    Matrix.toEuclideanLin (conjMat n) (-a + Matrix.toEuclideanLin (J₀ n) b +
        Matrix.toEuclideanLin (cBar A)ᵀ c) =
      -(Matrix.toEuclideanLin (conjMat n) a +
        Matrix.toEuclideanLin (J₀ n) (Matrix.toEuclideanLin (conjMat n) b) +
        Matrix.toEuclideanLin A (Matrix.toEuclideanLin (conjMat n) c)) := by
  have e1 : conjMat n * J₀ n = -(J₀ n * conjMat n) := conjMat_mul_J
  have e2 : conjMat n * (cBar A)ᵀ = -(A * conjMat n) := by
    rw [cBar_transpose, mul_neg, ← mul_assoc, ← mul_assoc, conjMat_mul_self, one_mul]
  rw [map_add, map_add, map_neg, ckp_toEL_mul, ckp_toEL_mul, e1, e2, ckp_toEL_neg, ckp_toEL_neg,
    ← ckp_toEL_mul, ← ckp_toEL_mul]
  abel

/-- `-C a + J₀ C b + Aᵀ C c = -C (a + J₀ b + S̄ c)`. -/
lemma ckp_key2 (A : Mat n) (a b c : Vec n) :
    -Matrix.toEuclideanLin (conjMat n) a +
        Matrix.toEuclideanLin (J₀ n) (Matrix.toEuclideanLin (conjMat n) b) +
        Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin (conjMat n) c) =
      -Matrix.toEuclideanLin (conjMat n) (a + Matrix.toEuclideanLin (J₀ n) b +
        Matrix.toEuclideanLin (cBar A) c) := by
  have e1 : conjMat n * J₀ n = -(J₀ n * conjMat n) := conjMat_mul_J
  have e2 : conjMat n * cBar A = -(Aᵀ * conjMat n) := by
    rw [cBar, mul_neg, ← mul_assoc, ← mul_assoc, conjMat_mul_self, one_mul]
  symm
  rw [map_add, map_add, ckp_toEL_mul (conjMat n) (J₀ n), ckp_toEL_mul (conjMat n) (cBar A), e1, e2,
    ckp_toEL_neg, ckp_toEL_neg, ← ckp_toEL_mul, ← ckp_toEL_mul]
  abel

/-! ### Conjugated test sections -/

lemma IsTestSection.ckp_conj {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) :
    IsTestSection (fun y => Matrix.toEuclideanLin (conjMat n) (φ y)) := by
  obtain ⟨R, hR⟩ := hφ.2.2
  refine ⟨(matCLM n (conjMat n)).contDiff.comp hφ.1, fun s t => by simp only [hφ.2.1], R,
    fun s t hs => by simp [hR s t hs]⟩

lemma ckp_partialS_conj {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) (x : ℝ × ℝ) :
    partialS (fun y => Matrix.toEuclideanLin (conjMat n) (φ y)) x =
      Matrix.toEuclideanLin (conjMat n) (partialS φ x) :=
  fderiv_matCLM_comp (conjMat n) (hφ.1.differentiable (by simp) x) (1, 0)

lemma ckp_partialT_conj {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) (x : ℝ × ℝ) :
    partialT (fun y => Matrix.toEuclideanLin (conjMat n) (φ y)) x =
      Matrix.toEuclideanLin (conjMat n) (partialT φ x) :=
  fderiv_matCLM_comp (conjMat n) (hφ.1.differentiable (by simp) x) (0, 1)

/-! ### Test triples -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma ckp_tt_mem {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : testTriple (p := p) hu ∈ W1p p n :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (testTriple_mem hu))

lemma ckp_tt_ae (S : ℝ × ℝ → Mat n) {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    crApply S (testTriple (p := p) hu) =ᵐ[cylMeasure] crOp S u :=
  crApply_ae_crOp S (hu.memLp (p := p)).coeFn_toLp (hu.memLp_partialS (p := p)).coeFn_toLp
    (hu.memLp_partialT (p := p)).coeFn_toLp

/-- A continuous linear functional on triples vanishing on test triples vanishes on `W^{1,p}`. -/
lemma ckp_W1p_le_ker (Λ : Triple n p →L[ℝ] ℝ)
    (h : ∀ u : ℝ × ℝ → Vec n, ∀ hu : IsTestSection u, ∀ w ∈ testTriples n p,
      (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u →
      (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u →
      (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u → Λ w = 0) :
    ∀ w ∈ W1p p n, Λ w = 0 := by
  have hle : W1p p n ≤ LinearMap.ker (Λ : Triple n p →ₗ[ℝ] ℝ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · refine Submodule.span_le.2 fun w hw => ?_
      obtain ⟨u, hu, h1, h2, h3⟩ := id hw
      exact h u hu w hw h1 h2 h3
    · exact Λ.isClosed_ker
  exact fun w hw => hle hw

end

end CauchyRiemannIndex

-- ===== Scratch/IPKer.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- The formal adjoint `D_S^* φ = -∂ₛφ + J₀ ∂ₜφ + Sᵀ φ`. -/
def ipkAdj (S : ℝ × ℝ → Mat n) (φ : ℝ × ℝ → Vec n) (x : ℝ × ℝ) : Vec n :=
  -partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
    Matrix.toEuclideanLin (S x)ᵀ (φ x)

lemma ipkAdj_continuous (S : ℝ × ℝ → Mat n) (hc : Continuous S) {φ : ℝ × ℝ → Vec n}
    (hφ : IsTestSection φ) : Continuous (ipkAdj S φ) := by
  have h3 : Continuous fun x => matCLM n (S x)ᵀ (φ x) :=
    (continuous_matCLM.comp hc.matrix_transpose).clm_apply hφ.continuous
  exact (hφ.continuous_partialS.neg.add
    ((matCLM n (J₀ n)).continuous.comp hφ.continuous_partialT)).add h3

lemma ipkAdj_vanish (S : ℝ × ℝ → Mat n) {φ : ℝ × ℝ → Vec n} (R : ℝ)
    (hR : ∀ s t, R < |s| → φ (s, t) = 0) :
    ∀ s t, R < |s| → ipkAdj S φ (s, t) = 0 := by
  intro s t hs
  simp [ipkAdj, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs, hR s t hs]

lemma ipkAdj_memLp {q : ℝ≥0∞} [Fact (1 ≤ q)] (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) : MemLp (ipkAdj S φ) q cylMeasure := by
  obtain ⟨R, hR⟩ := hφ.2.2
  exact memLp_of_vanish _ (ipkAdj_continuous S hc hφ) R (ipkAdj_vanish S R hR)

/-- Elements of `ker D_S ⊆ W^{1,p}` are weak solutions of `D_S η = 0`. -/
lemma ipk_weak {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) (hw : w ∈ W1p p n) (h0 : crsT S hc hb w = 0)
    (φ : ℝ × ℝ → Vec n) (hφ : IsTestSection φ) :
    ∫ x, inner ℝ (ipkAdj S φ x) (w.1 x) ∂cylMeasure = 0 := by
  set T : Triple n p →L[ℝ] LpCyl n p := crsT S hc hb
  set P := ckaPairL (μ := cylMeasure) (E := Vec n) (p := p) (q := q)
  set g1 : LpCyl n q := (hφ.memLp (p := q)).toLp φ
  set g2 : LpCyl n q := (ipkAdj_memLp (q := q) S hc hφ).toLp _
  let Λ : Triple n p →L[ℝ] ℝ :=
    (P.flip g1).comp T - (P.flip g2).comp (ContinuousLinearMap.fst ℝ _ _)
  have hΛ : ∀ v : Triple n p, Λ v = P (T v) g1 - P v.1 g2 := fun v => rfl
  have hW := ckp_W1p_le_ker Λ fun u hu v _ h1 h2 h3 => by
    have hA := crOp_formalAdjoint n S hc u φ hu hφ
    rw [hΛ, ckaPairL_apply, ckaPairL_apply, sub_eq_zero]
    have e1 : ∫ x, inner ℝ (T v x) (g1 x) ∂cylMeasure =
        ∫ x, inner ℝ (crOp S u x) (φ x) ∂cylMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [crsT_ae S hc hb v, crApply_ae_crOp S h1 h2 h3,
        (hφ.memLp (p := q)).coeFn_toLp] with x e1 e2 e3
      rw [e1, e2, e3]
    have e2 : ∫ x, inner ℝ (v.1 x) (g2 x) ∂cylMeasure =
        ∫ x, inner ℝ (u x) (ipkAdj S φ x) ∂cylMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [h1, (ipkAdj_memLp (q := q) S hc hφ).coeFn_toLp] with x e1 e2
      rw [e1, e2]
    rw [e1, e2, hA]
    rfl
  have h := hW w hw
  rw [hΛ, show T w = 0 from h0, map_zero, ContinuousLinearMap.zero_apply, zero_sub,
    neg_eq_zero, ckaPairL_apply] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [(ipkAdj_memLp (q := q) S hc hφ).coeFn_toLp] with x e
  rw [e, real_inner_comm]

/-- A kernel element whose first component lies in `L^r` gives a kernel element at exponent `r`. -/
lemma ipk_transfer {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1 < r) (hr' : r ≠ ⊤)
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    (w : Triple n p) (hw : w ∈ W1p p n) (h0 : crApply S w =ᵐ[cylMeasure] 0)
    (hmem : MemLp (w.1 : ℝ × ℝ → Vec n) r cylMeasure) :
    ∃ w' ∈ W1p r n, (w'.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] w.1 ∧
      crApply S w' =ᵐ[cylMeasure] 0 := by
  haveI : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  have hb := crs_Sbound hSplus hSminus hS
  have hT0 : crsT S hS.1 hb w = 0 :=
    Lp.ext ((crsT_ae S hS.1 hb w).trans (h0.trans (Lp.coeFn_zero _ _ _).symm))
  have hweak : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (S x)ᵀ (φ x)) (hmem.toLp _ x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) ((0 : LpCyl n r) x) ∂cylMeasure := by
    intro φ hφ
    have h := ipk_weak (q := p.conjExponent) S hS.1 hb w hw hT0 φ hφ
    have hR : ∫ x, inner ℝ (φ x) ((0 : LpCyl n r) x) ∂cylMeasure = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      filter_upwards [Lp.coeFn_zero (Vec n) r cylMeasure] with x hx
      rw [hx]; simp
    rw [hR, ← h]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x e
    rw [e]; rfl
  obtain ⟨w', hw', hw1, hw0⟩ := memW1p_of_weak_solution n r hr hr' _ _ hSplus hSminus S hS
    (hmem.toLp _) 0 hweak
  refine ⟨w', hw', ?_, hw0.trans (Lp.coeFn_zero _ _ _)⟩
  rw [hw1]
  exact hmem.coeFn_toLp

/-- `W^{1,p}` functions are in `L^{2p}`. -/
lemma ipk_up {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (w : Triple n p) (hw : w ∈ W1p p n) :
    MemLp (w.1 : ℝ × ℝ → Vec n) (2 * p) cylMeasure := by
  obtain ⟨C, hC⟩ := eLpNorm_two_mul_le_w1pNorm n p hp hp'
  have hcl : w ∈ closure (Submodule.span ℝ (testTriples n p) : Set (Triple n p)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hw
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  have ha' : ∀ j, a j ∈ testTriples n p := fun j => span_testTriples_subset (ha j)
  choose u hu h1 h2 h3 using ha'
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto a hlim)
  have hbd : ∀ j, eLpNorm ((a j).1 : ℝ × ℝ → Vec n) (2 * p) cylMeasure ≤
      C * ENNReal.ofReal (3 * B) := by
    intro j
    rw [eLpNorm_congr_ae (h1 j)]
    refine (hC (u j) (hu j)).trans ?_
    gcongr
    refine (crs_w1p_le (h1 j) (h2 j) (h3 j)).trans (ENNReal.ofReal_le_ofReal ?_)
    have := hB (a j) ⟨j, rfl⟩
    linarith
  have hl1 : Tendsto (fun j => (a j).1) atTop (𝓝 w.1) :=
    ((continuous_fst).tendsto w).comp hlim
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hl1).exists_seq_tendsto_ae
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2 * p)
    (fun i => Lp.aestronglyMeasurable (a (ns i)).1) _ hae
  refine ⟨Lp.aestronglyMeasurable _, lt_of_le_of_lt (hfat.trans
    (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun i => hbd (ns i)))) ?_⟩
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top

end

end CauchyRiemannIndex

-- ===== Scratch/IPDown.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### The cut-off `χ(s / a)` -/

/-- A smooth cut-off in `s`, equal to `1` on `[-1, 1]` and supported in `[-2, 2]`. -/
def ipdχ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

lemma ipdχ_one {t : ℝ} (h : |t| ≤ 1) : ipdχ t = 1 :=
  ipdχ.one_of_mem_closedBall (by rwa [Metric.mem_closedBall, Real.dist_0_eq_abs])

lemma ipdχ_zero {t : ℝ} (h : 2 < |t|) : ipdχ t = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  rw [ipdχ.tsupport_eq, Metric.mem_closedBall, Real.dist_0_eq_abs]
  change ¬ |t| ≤ 2
  linarith

lemma ipdχ_deriv_zero {t : ℝ} (h : 2 < |t|) : deriv (ipdχ : ℝ → ℝ) t = 0 := by
  have hU : IsOpen {y : ℝ | 2 < |y|} := isOpen_lt continuous_const continuous_abs
  have hev : (ipdχ : ℝ → ℝ) =ᶠ[𝓝 t] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds h) fun y hy => ipdχ_zero hy
  rw [hev.deriv_eq]; simp

lemma ipdχ_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv (ipdχ : ℝ → ℝ) t| ≤ M := by
  have hc : Continuous (deriv (ipdχ : ℝ → ℝ)) :=
    (ipdχ.contDiff (n := 1)).continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv (ipdχ : ℝ → ℝ)) := ipdχ.hasCompactSupport.deriv
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

/-- `c_a(s, t) = χ(s / a)`. -/
def ipdc (a : ℝ) (x : ℝ × ℝ) : ℝ := ipdχ (x.1 / a)

/-- `∂ₛ c_a(s, t) = χ'(s / a) / a`. -/
def ipdc' (a : ℝ) (x : ℝ × ℝ) : ℝ := deriv (ipdχ : ℝ → ℝ) (x.1 / a) / a

/-- `(s, t) ↦ s / a` as a continuous linear map. -/
def ipdL (a : ℝ) : ℝ × ℝ →L[ℝ] ℝ := a⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ

lemma ipdL_apply (a : ℝ) (x : ℝ × ℝ) : ipdL a x = x.1 / a := by
  simp [ipdL, div_eq_inv_mul]

lemma ipdc_eq (a : ℝ) : ipdc a = (ipdχ : ℝ → ℝ) ∘ ipdL a := by
  funext x; simp [ipdc, ipdL_apply]

lemma ipdc_contDiff (a : ℝ) : ContDiff ℝ ∞ (ipdc a) := by
  rw [ipdc_eq]; exact ipdχ.contDiff.comp (ipdL a).contDiff

lemma ipdc_hasFDerivAt (a : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (ipdc a) (deriv (ipdχ : ℝ → ℝ) (x.1 / a) • ipdL a) x := by
  rw [ipdc_eq]
  have h1 : HasDerivAt (ipdχ : ℝ → ℝ) (deriv (ipdχ : ℝ → ℝ) (x.1 / a)) (ipdL a x) := by
    rw [ipdL_apply]
    exact ((ipdχ.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  exact h1.comp_hasFDerivAt x (ipdL a).hasFDerivAt

lemma ipdc_bounds (a : ℝ) (x : ℝ × ℝ) : 0 ≤ ipdc a x ∧ ipdc a x ≤ 1 :=
  ⟨ipdχ.nonneg, ipdχ.le_one⟩

/-! ### Multiplying a test section by the cut-off -/

lemma ipd_partialS {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) (a : ℝ) (x : ℝ × ℝ) :
    partialS (fun y => ipdc a y • φ y) x = ipdc a x • partialS φ x + ipdc' a x • φ x := by
  have h := (ipdc_hasFDerivAt a x).smul ((hφ.1.differentiable (by simp) x).hasFDerivAt)
  have h3 : fderiv ℝ (fun y => ipdc a y • φ y) x = _ := h.fderiv
  rw [partialS, h3]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, ipdL_apply, ipdc']
  congr 1
  congr 1
  rw [smul_eq_mul]
  field_simp

lemma ipd_partialT {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) (a : ℝ) (x : ℝ × ℝ) :
    partialT (fun y => ipdc a y • φ y) x = ipdc a x • partialT φ x := by
  have h := (ipdc_hasFDerivAt a x).smul ((hφ.1.differentiable (by simp) x).hasFDerivAt)
  have h3 : fderiv ℝ (fun y => ipdc a y • φ y) x = _ := h.fderiv
  rw [partialT, h3]
  simp [ipdL_apply, partialT]

lemma ipd_test {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) (a : ℝ) :
    IsTestSection (fun y => ipdc a y • φ y) := by
  obtain ⟨R, hR⟩ := hφ.2.2
  refine ⟨(ipdc_contDiff a).smul hφ.1, fun s t => by simp only [ipdc, hφ.2.1], R,
    fun s t hs => by simp [hR s t hs]⟩

lemma ipd_adj (S : ℝ × ℝ → Mat n) {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) (a : ℝ)
    (x : ℝ × ℝ) :
    ipkAdj S (fun y => ipdc a y • φ y) x = ipdc a x • ipkAdj S φ x - ipdc' a x • φ x := by
  simp only [ipkAdj, ipd_partialS hφ, ipd_partialT hφ, map_smul, smul_add, smul_neg]
  abel

/-- Pairings of continuous sections vanishing for large `|s|` with `L^p` sections are
integrable. -/
lemma ipd_int {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : LpCyl n p) (g : ℝ × ℝ → Vec n) (hg : Continuous g)
    (R : ℝ) (hR : ∀ s t, R < |s| → g (s, t) = 0) :
    Integrable (fun x => inner ℝ (g x) (u x)) cylMeasure := by
  haveI : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  have hm : MemLp g p.conjExponent cylMeasure := memLp_of_vanish g hg R hR
  have h := cka_integrable (μ := cylMeasure) (p := p) (q := p.conjExponent) u (hm.toLp g)
  refine h.congr ?_
  filter_upwards [hm.coeFn_toLp] with x e
  rw [e, real_inner_comm]

end

end CauchyRiemannIndex

-- ===== Scratch/IPDown2.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma ipdc'_continuous (a : ℝ) : Continuous (ipdc' a) :=
  (((ipdχ.contDiff (n := 1)).continuous_deriv le_rfl).comp
    (continuous_fst.div_const a)).div_const a

lemma ipdc_continuous (a : ℝ) : Continuous (ipdc a) := (ipdc_contDiff a).continuous

/-- The truncation `c_a • u` of a kernel element weakly solves `D_S (c_a u) = c_a' u`. -/
lemma ipd_weak {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) (hw : w ∈ W1p p n) (h0 : crsT S hc hb w = 0) (a : ℝ)
    (φ : ℝ × ℝ → Vec n) (hφ : IsTestSection φ) :
    ∫ x, inner ℝ (ipkAdj S φ x) (ipdc a x • w.1 x) ∂cylMeasure =
      ∫ x, inner ℝ (φ x) (ipdc' a x • w.1 x) ∂cylMeasure := by
  have hψ := ipd_test hφ a
  have h := ipk_weak (q := q) S hc hb w hw h0 _ hψ
  obtain ⟨R, hR⟩ := hφ.2.2
  have hRψ : ∀ s t, R < |s| → ipdc a (s, t) • φ (s, t) = 0 := fun s t hs => by simp [hR s t hs]
  have hi1 : Integrable (fun x => inner ℝ (ipkAdj S (fun y => ipdc a y • φ y) x) (w.1 x))
      cylMeasure :=
    ipd_int w.1 _ (ipkAdj_continuous S hc hψ) R (ipkAdj_vanish S R hRψ)
  have hi2 : Integrable (fun x => inner ℝ (ipdc' a x • φ x) (w.1 x)) cylMeasure :=
    ipd_int w.1 _ ((ipdc'_continuous a).smul hφ.continuous) R
      (fun s t hs => by simp [hR s t hs])
  have hpt : ∀ x, inner ℝ (ipkAdj S φ x) (ipdc a x • w.1 x) =
      inner ℝ (ipkAdj S (fun y => ipdc a y • φ y) x) (w.1 x) +
        inner ℝ (ipdc' a x • φ x) (w.1 x) := by
    intro x
    rw [ipd_adj S hφ a x, inner_sub_left, inner_smul_left, inner_smul_left, inner_smul_right]
    simp
  have hpt2 : ∀ x, inner ℝ (ipdc' a x • φ x) (w.1 x) = inner ℝ (φ x) (ipdc' a x • w.1 x) := by
    intro x
    rw [inner_smul_left, inner_smul_right]
    simp
  simp_rw [hpt]
  rw [integral_add hi1 hi2, h, zero_add]
  simp_rw [hpt2]

lemma ipd_measure {a : ℝ} (ha : 0 ≤ a) :
    cylMeasure (Icc (-(2 * a)) (2 * a) ×ˢ (univ : Set ℝ)) ≤ ENNReal.ofReal (4 * a) := by
  unfold cylMeasure
  rw [Measure.restrict_apply (measurableSet_Icc.prod MeasurableSet.univ), prod_inter_prod,
    univ_inter, inter_univ, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    Real.volume_Ico]
  simp only [sub_zero, ENNReal.ofReal_one, mul_one]
  exact le_of_eq (by ring_nf)

lemma ipd_vanish {a : ℝ} (ha : 0 < a) {x : ℝ × ℝ} (hx : x ∉ Icc (-(2 * a)) (2 * a) ×ˢ (univ : Set ℝ)) :
    ipdc a x = 0 ∧ ipdc' a x = 0 := by
  have h : 2 < |x.1 / a| := by
    rw [abs_div, abs_of_pos ha, lt_div_iff₀ ha]
    by_contra h'
    push_neg at h'
    exact hx ⟨abs_le.1 (by linarith), mem_univ _⟩
  exact ⟨ipdχ_zero h, by simp [ipdc', ipdχ_deriv_zero h]⟩

/-- The `L^r` norm of the truncations, for `r ≤ p`, is bounded uniformly in `a`. -/
lemma ipd_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp' : p ≠ ⊤) {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1 < r)
    (hrp : r ≤ p)
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (R : ℝ) (c : ℝ≥0)
    (hest : ∀ w ∈ W1p r n, ‖w‖ ≤ c * ‖crsT S hS.1 hb w‖ + c * ‖crsK n r R w‖)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ t : ℝ, |deriv (ipdχ : ℝ → ℝ) t| ≤ M)
    (w : Triple n p) (hw : w ∈ W1p p n) (hT0 : crsT S hS.1 hb w = 0)
    (a : ℝ) (haR : R ≤ a) (ha1 : 1 ≤ a) :
    eLpNorm (fun x => ipdc a x • w.1 x) r cylMeasure ≤
      c * (ENNReal.ofReal (4 * M) * eLpNorm w.1 p cylMeasure +
        eLpNorm w.1 r (crsμ R)) := by
  haveI : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  have hrt : r ≠ ⊤ := ne_top_of_le_ne_top hp' hrp
  have ha0 : 0 < a := by linarith
  set K : Set (ℝ × ℝ) := Icc (-(2 * a)) (2 * a) ×ˢ (univ : Set ℝ) with hK
  have hKm : cylMeasure K ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (ipd_measure ha0.le)
  have hu := Lp.memLp w.1
  have hum := Lp.aestronglyMeasurable w.1
  have hηm : AEStronglyMeasurable (fun x => ipdc a x • w.1 x) cylMeasure :=
    (ipdc_continuous a).aestronglyMeasurable.smul hum
  have hfm : AEStronglyMeasurable (fun x => ipdc' a x • w.1 x) cylMeasure :=
    (ipdc'_continuous a).aestronglyMeasurable.smul hum
  have hηb : ∀ x, ‖ipdc a x • w.1 x‖ ≤ 1 * ‖w.1 x‖ := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg (ipdc_bounds a x).1]
    exact mul_le_mul_of_nonneg_right (ipdc_bounds a x).2 (norm_nonneg _)
  have hfb : ∀ x, ‖ipdc' a x • w.1 x‖ ≤ M / a * ‖w.1 x‖ := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, ipdc', abs_div, abs_of_pos ha0]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hM _) ha0.le) (norm_nonneg _)
  have hη : MemLp (fun x => ipdc a x • w.1 x) r cylMeasure :=
    (hu.of_le_mul hηm (Eventually.of_forall hηb)).mono_exponent_of_measure_support_ne_top
      (fun x hx => by simp [(ipd_vanish ha0 hx).1]) hKm hrp
  have hf : MemLp (fun x => ipdc' a x • w.1 x) r cylMeasure :=
    (hu.of_le_mul hfm (Eventually.of_forall hfb)).mono_exponent_of_measure_support_ne_top
      (fun x hx => by simp [(ipd_vanish ha0 hx).2]) hKm hrp
  -- the weak equation and regularity
  have hweak : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (S x)ᵀ (φ x)) (hη.toLp _ x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) (hf.toLp _ x) ∂cylMeasure := by
    intro φ hφ
    have h := ipd_weak (q := p.conjExponent) S hS.1 hb w hw hT0 a φ hφ
    have e1 : ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (S x)ᵀ (φ x)) (hη.toLp _ x) ∂cylMeasure =
        ∫ x, inner ℝ (ipkAdj S φ x) (ipdc a x • w.1 x) ∂cylMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [hη.coeFn_toLp] with x e
      rw [e]; rfl
    have e2 : ∫ x, inner ℝ (φ x) (hf.toLp _ x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) (ipdc' a x • w.1 x) ∂cylMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [hf.coeFn_toLp] with x e
      rw [e]
    rw [e1, e2, h]
  obtain ⟨w', hw', hw1, hw0⟩ := memW1p_of_weak_solution n r hr hrt _ _ hSplus hSminus S hS
    (hη.toLp _) (hf.toLp _) hweak
  have hT : crsT S hS.1 hb w' = hf.toLp _ := Lp.ext ((crsT_ae S hS.1 hb w').trans hw0)
  have hest' := hest w' hw'
  -- the three norms
  have nη : eLpNorm (fun x => ipdc a x • w.1 x) r cylMeasure = ENNReal.ofReal ‖w'.1‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), hw1]
    exact (eLpNorm_congr_ae hη.coeFn_toLp).symm
  have nT : ENNReal.ofReal ‖crsT S hS.1 hb w'‖ = eLpNorm (fun x => ipdc' a x • w.1 x) r cylMeasure := by
    rw [hT, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    exact eLpNorm_congr_ae hf.coeFn_toLp
  have nK : ENNReal.ofReal ‖crsK n r R w'‖ = eLpNorm w.1 r (crsμ R) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    refine eLpNorm_congr_ae ?_
    have h1 : (w'.1 : ℝ × ℝ → Vec n) =ᵐ[crsμ R] fun x => ipdc a x • w.1 x := by
      rw [hw1]; exact ae_restrict_of_ae hη.coeFn_toLp
    filter_upwards [crsK_ae R w', h1, ae_restrict_mem (μ := cylMeasure)
      (measurableSet_Icc.prod MeasurableSet.univ)] with x e1 e2 hx
    rw [e1, e2]
    have : |x.1 / a| ≤ 1 := by
      rw [abs_div, abs_of_pos ha0, div_le_one ha0]
      exact (abs_le.2 hx.1).trans haR
    simp [ipdc, ipdχ_one this]
  -- Hölder on the support of `c_a'`
  have hfp : eLpNorm (fun x => ipdc' a x • w.1 x) r cylMeasure ≤
      ENNReal.ofReal (4 * M) * eLpNorm w.1 p cylMeasure := by
    have hsupp : Function.support (fun x => ipdc' a x • w.1 x) ⊆ K := by
      intro x hx
      by_contra h
      exact hx (by simp [(ipd_vanish ha0 h).2])
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    have hα0 : 0 ≤ 1 / r.toReal - 1 / p.toReal := by
      have h1 : 0 < r.toReal := ENNReal.toReal_pos (zero_lt_one.trans hr).ne' hrt
      have h2 : r.toReal ≤ p.toReal := ENNReal.toReal_mono hp' hrp
      rw [sub_nonneg]; exact one_div_le_one_div_of_le h1 h2
    have hα1 : 1 / r.toReal - 1 / p.toReal ≤ 1 := by
      have h1 : 1 ≤ r.toReal := by
        have := ENNReal.toReal_mono hrt hr.le; simpa using this
      have h3 : 0 ≤ 1 / p.toReal := by positivity
      have h4 : 1 / r.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
      linarith
    calc eLpNorm (fun x => ipdc' a x • w.1 x) r (cylMeasure.restrict K)
        ≤ eLpNorm (fun x => ipdc' a x • w.1 x) p (cylMeasure.restrict K) *
            (cylMeasure.restrict K) univ ^ (1 / r.toReal - 1 / p.toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hrp hfm.restrict
      _ ≤ (ENNReal.ofReal (M / a) * eLpNorm w.1 p cylMeasure) *
            ENNReal.ofReal (4 * a) := by
          gcongr
          · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
              (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall hfb) p)
          · rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
            calc cylMeasure K ^ (1 / r.toReal - 1 / p.toReal)
                ≤ ENNReal.ofReal (4 * a) ^ (1 / r.toReal - 1 / p.toReal) :=
                  ENNReal.rpow_le_rpow (ipd_measure ha0.le) hα0
              _ = ENNReal.ofReal ((4 * a) ^ (1 / r.toReal - 1 / p.toReal)) :=
                  ENNReal.ofReal_rpow_of_nonneg (by positivity) hα0
              _ ≤ ENNReal.ofReal (4 * a) :=
                  ENNReal.ofReal_le_ofReal (Real.rpow_le_self_of_one_le (by linarith) hα1)
      _ = ENNReal.ofReal (4 * M) * eLpNorm w.1 p cylMeasure := by
          rw [mul_comm (ENNReal.ofReal (M / a)), mul_assoc, ← ENNReal.ofReal_mul
            (by positivity), show M / a * (4 * a) = 4 * M by field_simp, mul_comm]
  -- assemble
  have h3 : ENNReal.ofReal ‖w'.1‖ ≤ ENNReal.ofReal ‖w'‖ := ENNReal.ofReal_le_ofReal (norm_fst_le w')
  rw [nη]
  refine h3.trans ((ENNReal.ofReal_le_ofReal hest').trans ?_)
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul c.coe_nonneg,
    ENNReal.ofReal_mul c.coe_nonneg, nT, nK, ENNReal.ofReal_coe_nnreal, mul_add]
  gcongr

end

end CauchyRiemannIndex

-- ===== Scratch/IPMain.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- Kernel elements, for exponents `r ≤ p`, have first component in `L^r`. -/
lemma ipm_down {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp' : p ≠ ⊤) {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hr : 1 < r) (hrp : r ≤ p)
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (w : Triple n p) (hw : w ∈ W1p p n) (h0 : crApply S w =ᵐ[cylMeasure] 0) :
    MemLp (w.1 : ℝ × ℝ → Vec n) r cylMeasure := by
  have hrt : r ≠ ⊤ := ne_top_of_le_ne_top hp' hrp
  have hb := crs_Sbound hSplus hSminus hS
  have hT0 : crsT S hS.1 hb w = 0 :=
    Lp.ext ((crsT_ae S hS.1 hb w).trans (h0.trans (Lp.coeFn_zero _ _ _).symm))
  obtain ⟨R, c, hest0⟩ := global_estimate n r hr hrt Splus Sminus hSplus hSminus S hS hplus hminus
  have hest := crs_estimate (p := r) S hS.1 hb R c hest0
  obtain ⟨M, hM0, hM⟩ := ipdχ_deriv_bound
  set B : ℝ := max R 1
  set A : ℝ≥0∞ := c * (ENNReal.ofReal (4 * M) * eLpNorm w.1 p cylMeasure +
    eLpNorm w.1 r (crsμ R))
  have hKfin : eLpNorm (w.1 : ℝ × ℝ → Vec n) r (crsμ R) < ⊤ := by
    have hμ : (crsμ R) univ ≠ ⊤ := by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
      refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((measure_mono ?_).trans (ipd_measure (abs_nonneg R)))
      intro x hx
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩
      · linarith [hx.1.1, le_abs_self R, abs_nonneg R]
      · linarith [hx.1.2, le_abs_self R, abs_nonneg R]
    exact (((Lp.memLp w.1).restrict _).mono_exponent_of_measure_support_ne_top
      (s := univ) (fun x hx => absurd (mem_univ x) hx) hμ hrp).2
  have hA : A < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.2 ⟨?_, hKfin⟩)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top _)
  set a : ℕ → ℝ := fun k => k + B
  have haR : ∀ k, R ≤ a k := fun k => by
    have := le_max_left R 1; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; simp only [a]; linarith
  have ha1 : ∀ k, 1 ≤ a k := fun k => by
    have := le_max_right R 1; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; simp only [a]; linarith
  have hbd : ∀ k, eLpNorm (fun x => ipdc (a k) x • w.1 x) r cylMeasure ≤ A := fun k =>
    ipd_bound hp' hr hrp hSplus hSminus hS hb R c hest M hM0 hM w hw hT0 (a k) (haR k) (ha1 k)
  have hlim : ∀ x, Tendsto (fun k => ipdc (a k) x • w.1 x) atTop (𝓝 (w.1 x)) := by
    intro x
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|x.1|⌉₊] with k hk
    have hk' : |x.1| ≤ k := (Nat.le_ceil _).trans (Nat.cast_le.2 hk)
    have ha0 : 0 < a k := by linarith [ha1 k]
    have : |x.1 / a k| ≤ 1 := by
      rw [abs_div, abs_of_pos ha0, div_le_one ha0]
      have := le_max_right R 1
      simp only [a]; linarith
    simp [ipdc, ipdχ_one this]
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := r)
    (fun k => (ipdc_continuous (a k)).aestronglyMeasurable.smul (Lp.aestronglyMeasurable w.1))
    _ (Eventually.of_forall hlim)
  refine ⟨Lp.aestronglyMeasurable _, lt_of_le_of_lt (hfat.trans
    (Filter.liminf_le_of_frequently_le' (Frequently.of_forall hbd))) hA⟩

/-- Kernel elements, for exponents `p ≤ r ≤ 2ᵐ p`, have first component in `L^r`. -/
lemma ipm_up_aux (m : ℕ) :
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ⊤ →
    ∀ {Splus Sminus : ℝ → Mat n}, IsSymLoop Splus → IsSymLoop Sminus →
    ∀ {S : ℝ × ℝ → Mat n}, IsAsymptoticTo S Splus Sminus →
    ∀ w : Triple n p, w ∈ W1p p n → crApply S w =ᵐ[cylMeasure] 0 →
    ∀ r : ℝ≥0∞, p ≤ r → r ≤ 2 ^ m * p → MemLp (w.1 : ℝ × ℝ → Vec n) r cylMeasure := by
  induction m with
  | zero =>
    intro p _ hp hp' Splus Sminus hSplus hSminus S hS w hw h0 r hpr hrp
    have : r = p := le_antisymm (by simpa using hrp) hpr
    subst this
    exact Lp.memLp w.1
  | succ m ih =>
    intro p _ hp hp' Splus Sminus hSplus hSminus S hS w hw h0 r hpr hrp
    have h2p : MemLp (w.1 : ℝ × ℝ → Vec n) (2 * p) cylMeasure := ipk_up hp hp' w hw
    have h2pt : 2 * p ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hp'
    have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
    rcases le_total r (2 * p) with h | h
    · exact memLp_of_le_of_le hp0 hpr h h2pt (Lp.memLp w.1) h2p
    · haveI : Fact (1 ≤ 2 * p) := ⟨by
        calc (1 : ℝ≥0∞) ≤ p := hp.le
          _ ≤ 2 * p := by
            calc p = 1 * p := (one_mul p).symm
              _ ≤ 2 * p := by gcongr; norm_num⟩
      have h1 : 1 < 2 * p :=
        lt_of_lt_of_le hp (by calc p = 1 * p := (one_mul p).symm
          _ ≤ 2 * p := by gcongr; norm_num)
      obtain ⟨w', hw', hw1, hw0⟩ := ipk_transfer hp hp' h1 h2pt hSplus hSminus hS w hw h0 h2p
      have hr' : r ≤ 2 ^ m * (2 * p) := by
        calc r ≤ 2 ^ (m + 1) * p := hrp
          _ = 2 ^ m * (2 * p) := by rw [pow_succ, mul_assoc]
      have := ih (2 * p) h1 h2pt hSplus hSminus hS w' hw' hw0 r h hr'
      exact (memLp_congr_ae hw1).1 this

lemma ipm_up {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤) {r : ℝ≥0∞} (hpr : p ≤ r)
    (hr' : r ≠ ⊤)
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    (w : Triple n p) (hw : w ∈ W1p p n) (h0 : crApply S w =ᵐ[cylMeasure] 0) :
    MemLp (w.1 : ℝ × ℝ → Vec n) r cylMeasure := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt r.toReal (by norm_num : (1 : ℝ) < 2)
  refine ipm_up_aux m p hp hp' hSplus hSminus hS w hw h0 r hpr ?_
  calc r = ENNReal.ofReal r.toReal := (ENNReal.ofReal_toReal hr').symm
    _ ≤ ENNReal.ofReal (2 ^ m) := ENNReal.ofReal_le_ofReal hm.le
    _ = 2 ^ m := by rw [ENNReal.ofReal_pow (by norm_num)]; simp
    _ = 2 ^ m * 1 := (mul_one _).symm
    _ ≤ 2 ^ m * p := by gcongr

lemma ipm_mem {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    {w : Triple n p} (hw : w ∈ crKernel p S) :
    w ∈ W1p p n ∧ crsT S hS.1 (crs_Sbound hSplus hSminus hS) w = 0 := by
  have hb := crs_Sbound hSplus hSminus hS
  have hK : crKernel p S ≤
      W1p p n ⊓ LinearMap.ker (crsT (p := p) S hS.1 hb : Triple n p →ₗ[ℝ] LpCyl n p) := by
    refine Submodule.span_le.2 fun w hw => ⟨hw.1, ?_⟩
    show crsT S hS.1 hb w = 0
    exact Lp.ext ((crsT_ae S hS.1 hb w).trans (hw.2.trans (Lp.coeFn_zero _ _ _).symm))
  exact hK hw

lemma ipm_ae_zero {p : ℝ≥0∞} [Fact (1 ≤ p)] {S : ℝ × ℝ → Mat n} (hc : Continuous S)
    {hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖}
    {w : Triple n p} (h : crsT S hc hb w = 0) : crApply S w =ᵐ[cylMeasure] 0 := by
  refine (crsT_ae S hc hb w).symm.trans ?_
  rw [h]; exact Lp.coeFn_zero _ _ _

/-- Kernel elements at exponent `p` give kernel elements at every exponent `r`. -/
lemma ipm_transfer {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1 < r) (hr' : r ≠ ⊤)
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (w : Triple n p) (hw : w ∈ crKernel p S) :
    ∃ w' ∈ crKernel r S, (w'.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] w.1 := by
  obtain ⟨hw1, hT⟩ := ipm_mem hSplus hSminus hS hw
  have h0 := ipm_ae_zero hS.1 hT
  have hmem : MemLp (w.1 : ℝ × ℝ → Vec n) r cylMeasure := by
    rcases le_total r p with h | h
    · exact ipm_down hp' hr h hSplus hSminus hS hplus hminus w hw1 h0
    · exact ipm_up hp hp' h hr' hSplus hSminus hS w hw1 h0
  obtain ⟨w', hw', he, h0'⟩ := ipk_transfer hp hp' hr hr' hSplus hSminus hS w hw1 h0 hmem
  exact ⟨w', Submodule.subset_span ⟨hw', h0'⟩, he⟩

end

end CauchyRiemannIndex

-- ===== Scratch/IPFinal.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- A kernel element is determined by its first component. -/
lemma ipf_uniq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    {y y' : Triple n p} (hy : y ∈ crKernel p S) (hy' : y' ∈ crKernel p S)
    (he : (y.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] y'.1) : y = y' := by
  have hb := crs_Sbound hSplus hSminus hS
  obtain ⟨R, c, hest⟩ := global_estimate n p hp hp' Splus Sminus hSplus hSminus S hS hplus hminus
  have hz : y - y' ∈ crKernel p S := (crKernel p S).sub_mem hy hy'
  obtain ⟨hzW, hzT⟩ := ipm_mem hSplus hSminus hS hz
  have h1 : (y - y').1 = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub y.1 y'.1, he, Lp.coeFn_zero (Vec n) p cylMeasure] with x e1 e2 e3
    rw [Prod.fst_sub, e1, Pi.sub_apply, e2, sub_self, e3]; rfl
  have hK : crsK n p R (y - y') = 0 := by simp [crsK, h1]
  have := crs_estimate S hS.1 hb R c hest _ hzW
  have hle : ‖y - y'‖ ≤ 0 := by
    refine this.trans (le_of_eq ?_)
    rw [hzT, hK]; simp
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- `dim ker D_S^{(p)} ≤ dim ker D_S^{(r)}`. -/
lemma ipf_finrank_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1 < r) (hr' : r ≠ ⊤)
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus) :
    Module.finrank ℝ (crKernel p S) ≤ Module.finrank ℝ (crKernel r S) := by
  have htr : ∀ x : crKernel p S, ∃ y : crKernel r S,
      ((y : Triple n r).1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] (x : Triple n p).1 := by
    intro x
    obtain ⟨w', hw', he⟩ :=
      ipm_transfer hp hp' hr hr' hSplus hSminus hS hplus hminus (x : Triple n p) x.2
    exact ⟨⟨w', hw'⟩, he⟩
  choose F hF using htr
  have uq := fun {y y' : Triple n r} (hy : y ∈ crKernel r S) (hy' : y' ∈ crKernel r S) he =>
    ipf_uniq hr hr' hSplus hSminus hS hplus hminus hy hy' he
  let Φ : crKernel p S →ₗ[ℝ] crKernel r S :=
    { toFun := F
      map_add' := fun x y => by
        apply Subtype.ext
        refine uq (F (x + y)).2 (F x + F y).2 ?_
        filter_upwards [hF (x + y), hF x, hF y, Lp.coeFn_add ((x : Triple n p).1) (y : Triple n p).1,
          Lp.coeFn_add ((F x : Triple n r).1) (F y : Triple n r).1] with z e1 e2 e3 e4 e5
        rw [e1, Submodule.coe_add, Prod.fst_add, e4, Submodule.coe_add, Prod.fst_add, e5,
          Pi.add_apply, Pi.add_apply, e2, e3]
      map_smul' := fun c x => by
        apply Subtype.ext
        refine uq (F (c • x)).2 (c • F x).2 ?_
        filter_upwards [hF (c • x), hF x, Lp.coeFn_smul c ((x : Triple n p).1),
          Lp.coeFn_smul c ((F x : Triple n r).1)] with z e1 e2 e3 e4
        rw [e1, Submodule.coe_smul, Prod.smul_fst, e3, RingHom.id_apply, Submodule.coe_smul,
          Prod.smul_fst, e4, Pi.smul_apply, Pi.smul_apply, e2] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hx0 : F x = 0 := hx
    apply Subtype.ext
    refine ipf_uniq hp hp' hSplus hSminus hS hplus hminus x.2 (crKernel p S).zero_mem ?_
    have h := hF x
    rw [hx0] at h
    filter_upwards [h.symm, Lp.coeFn_zero (Vec n) r cylMeasure,
      Lp.coeFn_zero (Vec n) p cylMeasure] with z e1 e2 e3
    rw [e1]
    simp only [ZeroMemClass.coe_zero, Prod.fst_zero] at e2 ⊢
  haveI : FiniteDimensional ℝ (crKernel r S) :=
    (semiFredholm n r hr hr' Splus Sminus hSplus hSminus S hS hplus hminus).1
  exact LinearMap.finrank_le_finrank_of_injective hinj

lemma ipf_finrank_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1 < r) (hr' : r ≠ ⊤)
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus) :
    Module.finrank ℝ (crKernel p S) = Module.finrank ℝ (crKernel r S) :=
  le_antisymm (ipf_finrank_le hp hp' hr hr' hSplus hSminus hS hplus hminus)
    (ipf_finrank_le hr hr' hp hp' hSplus hSminus hS hplus hminus)

/-- The cokernel dimension through the adjoint kernel at the conjugate exponent. -/
lemma ipf_coker {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus) :
    ∃ (q : ℝ≥0∞) (_ : Fact (1 ≤ q)), 1 < q ∧ q ≠ ⊤ ∧
      Module.finrank ℝ (LpCyl n p ⧸ crRange p S) =
        Module.finrank ℝ (crKernel q (fun x => -(conjMat n * (S x)ᵀ * conjMat n))) := by
  haveI hq : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  have hH : p.HolderConjugate p.conjExponent := inferInstance
  have hpq : 1 / p + 1 / p.conjExponent = 1 := by
    simpa [one_div] using hH.inv_add_inv_eq_one
  have hq1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).1 (lt_top_iff_ne_top.2 hp')
  have hqt : p.conjExponent ≠ ⊤ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one p.conjExponent p).2 hp.ne'
  exact ⟨p.conjExponent, hq, hq1, hqt, (cokernel_eq_kernel_adjoint n p hp hp' Splus Sminus
    hSplus hSminus S hS hplus hminus p.conjExponent hpq).2⟩

theorem index_independent_of_p_aux (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus)
    (hminus : IsNondegenerate Sminus)
    (p₂ : ℝ≥0∞) [Fact (1 ≤ p₂)] (hp₂ : 1 < p₂) (hp₂' : p₂ ≠ ⊤) :
    Module.finrank ℝ (crKernel p S) = Module.finrank ℝ (crKernel p₂ S) ∧
      crIndex p S = crIndex p₂ S := by
  have hk := ipf_finrank_eq hp hp' hp₂ hp₂' hSplus hSminus hS hplus hminus
  refine ⟨hk, ?_⟩
  have hSb := conj_isAsymptoticTo n S Splus Sminus hS
  obtain ⟨hbp, hnbp⟩ := conj_loop_isSymLoop_isNondegenerate n Splus hSplus hplus
  obtain ⟨hbm, hnbm⟩ := conj_loop_isSymLoop_isNondegenerate n Sminus hSminus hminus
  obtain ⟨q, hq, hq1, hqt, hc⟩ := ipf_coker hp hp' hSplus hSminus hS hplus hminus
  obtain ⟨q₂, hq₂, hq₂1, hq₂t, hc₂⟩ := ipf_coker hp₂ hp₂' hSplus hSminus hS hplus hminus
  have hkb := ipf_finrank_eq hq1 hqt hq₂1 hq₂t hbp hbm hSb hnbp hnbm
  unfold crIndex
  rw [hc, hc₂, hk, hkb]

end

end CauchyRiemannIndex

-- ===== Scratch/IPSol.lean =====
open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

open CauchyRiemannIndex in
theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (p₂ : ℝ≥0∞) [Fact (1 ≤ p₂)] (hp₂ : 1 < p₂) (hp₂' : p₂ ≠ ⊤) :
    Module.finrank ℝ (crKernel p S) = Module.finrank ℝ (crKernel p₂ S) ∧
      crIndex p S = crIndex p₂ S :=
  index_independent_of_p_aux n p hp hp' Splus Sminus hSplus hSminus S hS hplus hminus p₂ hp₂ hp₂'
