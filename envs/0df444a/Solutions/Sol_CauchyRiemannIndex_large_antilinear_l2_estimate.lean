-- Prove2me | solution 1 for CauchyRiemannIndex.large_antilinear_l2_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:10:53.406765+00:00
-- url     : https://prove2.me/submissions/613996b4-a593-4695-a959-7f6a6f2762ce

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Theorems.Thm_CauchyRiemannIndex_global_estimate
import Theorems.Thm_CauchyRiemannIndex_compact_restriction
import Theorems.Thm_CauchyRiemannIndex_finiteDimensional_ker_isClosed_range_of_estimate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Theorems.Thm_CauchyRiemannIndex_crOp_energy_identity
import Theorems.Thm_CauchyRiemannIndex_crOp_formalAdjoint
import Mathlib.MeasureTheory.Function.L2Space



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

/-!
# Large antilinear perturbations: coordinates on `ℝ²` and slice derivatives

Coordinate formulas for `Vec 1 = ℝ²` (inner product, norm, `J₀`, `antilinearMat`) and
integration-by-parts helpers on the cylinder for slice derivatives.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace LAPC

/-- The `q`-coordinate index. -/
abbrev iq : Fin 1 ⊕ Fin 1 := Sum.inl 0
/-- The `p`-coordinate index. -/
abbrev ip : Fin 1 ⊕ Fin 1 := Sum.inr 0

lemma vec1_norm_sq (v : Vec 1) : ‖v‖ ^ 2 = v iq ^ 2 + v ip ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fintype.sum_sum_type]

lemma vec1_inner (v w : Vec 1) : inner ℝ v w = v iq * w iq + v ip * w ip := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, mul_comm]

lemma vec1_ext {v w : Vec 1} (h1 : v iq = w iq) (h2 : v ip = w ip) : v = w := by
  ext i
  rcases i with i | i <;> rw [Fin.fin_one_eq_zero i] <;> assumption

lemma toEL_apply (A : Mat 1) (v : Vec 1) (i : Fin 1 ⊕ Fin 1) :
    Matrix.toEuclideanLin A v i = A i iq * v iq + A i ip * v ip := by
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

lemma J_q (v : Vec 1) : Matrix.toEuclideanLin (J₀ 1) v iq = - v ip := by
  rw [toEL_apply]; simp [Matrix.J]

lemma J_p (v : Vec 1) : Matrix.toEuclideanLin (J₀ 1) v ip = v iq := by
  rw [toEL_apply]; simp [Matrix.J]

lemma A_q (b : ℂ) (v : Vec 1) :
    Matrix.toEuclideanLin (antilinearMat b) v iq = b.re * v iq + b.im * v ip := by
  rw [toEL_apply]; simp [antilinearMat]

lemma A_p (b : ℂ) (v : Vec 1) :
    Matrix.toEuclideanLin (antilinearMat b) v ip = b.im * v iq - b.re * v ip := by
  rw [toEL_apply]; simp [antilinearMat]; ring

lemma add_apply' (v w : Vec 1) (i : Fin 1 ⊕ Fin 1) : (v + w) i = v i + w i := rfl

lemma smul_apply' (c : ℝ) (v : Vec 1) (i : Fin 1 ⊕ Fin 1) : (c • v) i = c * v i := rfl

lemma norm_A (b : ℂ) (v : Vec 1) :
    ‖Matrix.toEuclideanLin (antilinearMat b) v‖ = ‖b‖ * ‖v‖ := by
  have h : ‖Matrix.toEuclideanLin (antilinearMat b) v‖ ^ 2 = (‖b‖ * ‖v‖) ^ 2 := by
    rw [vec1_norm_sq, mul_pow, vec1_norm_sq, A_q, A_p, Complex.sq_norm, Complex.normSq_apply]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

lemma abs_comp_le (v : Vec 1) (i : Fin 1 ⊕ Fin 1) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le (p := 2) v i
  simpa using this

/-- Continuity of a coordinate. -/
lemma continuous_comp_apply {X : Type*} [TopologicalSpace X] {f : X → Vec 1} (hf : Continuous f)
    (i : Fin 1 ⊕ Fin 1) : Continuous fun x => f x i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hf

/-! ### Slice derivatives -/

lemma hasDerivAt_s {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × ℝ → E}
    (hf : Differentiable ℝ f) (s t : ℝ) :
    HasDerivAt (fun s => f (s, t)) (fderiv ℝ f (s, t) (1, 0)) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  exact (hf (s, t)).hasFDerivAt.comp_hasDerivAt s h1

lemma hasDerivAt_t {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × ℝ → E}
    (hf : Differentiable ℝ f) (s t : ℝ) :
    HasDerivAt (fun t => f (s, t)) (fderiv ℝ f (s, t) (0, 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  exact (hf (s, t)).hasFDerivAt.comp_hasDerivAt t h1

lemma hasDerivAt_comp_apply {g : ℝ → Vec 1} {g' : Vec 1} {s : ℝ} (h : HasDerivAt g g' s)
    (i : Fin 1 ⊕ Fin 1) : HasDerivAt (fun s => g s i) (g' i) s :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt s h

lemma hasDerivAt_re {g : ℝ → ℂ} {g' : ℂ} {s : ℝ} (h : HasDerivAt g g' s) :
    HasDerivAt (fun s => (g s).re) g'.re s :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h

lemma hasDerivAt_im {g : ℝ → ℂ} {g' : ℂ} {s : ℝ} (h : HasDerivAt g g' s) :
    HasDerivAt (fun s => (g s).im) g'.im s :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt s h

/-- `∫ g = 0` over the cylinder when `g = ∂ₛF` slice-wise, with `g` continuous and both `g` and
`F` vanishing for large `|s|`. -/
lemma integral_s_eq_zero_of_hasDerivAt (g F : ℝ × ℝ → ℝ) (hg : Continuous g) (R : ℝ)
    (hgR : ∀ s t, R < |s| → g (s, t) = 0) (hFR : ∀ s t, R < |s| → F (s, t) = 0)
    (hF : ∀ s t, HasDerivAt (fun s => F (s, t)) (g (s, t)) s) :
    ∫ x, g x ∂cylMeasure = 0 := by
  have hI : Integrable g cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish g hg R hgR
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod_symm _ hI]
  have h : ∀ t : ℝ, ∫ s, g (s, t) = 0 := by
    intro t
    have hFc : Continuous fun s => F (s, t) :=
      continuous_iff_continuousAt.2 fun s => (hF s t).continuousAt
    refine integral_eq_zero_of_hasDerivAt_of_integrable (fun s => hF s t) ?_ ?_
    · exact (hg.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish R fun s hs => hgR s t hs)
    · exact hFc.integrable_of_hasCompactSupport (hasCompactSupport_of_vanish R fun s hs => hFR s t hs)
  simp [h]

/-- `∫ g = 0` over the cylinder when `g = ∂ₜF` slice-wise, with `F` `1`-periodic in `t`. -/
lemma integral_t_eq_zero_of_hasDerivAt (g F : ℝ × ℝ → ℝ) (hg : Continuous g) (R : ℝ)
    (hgR : ∀ s t, R < |s| → g (s, t) = 0) (hper : ∀ s t, F (s, t + 1) = F (s, t))
    (hF : ∀ s t, HasDerivAt (fun t => F (s, t)) (g (s, t)) t) :
    ∫ x, g x ∂cylMeasure = 0 := by
  have hI : Integrable g cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish g hg R hgR
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod _ hI]
  have h : ∀ s : ℝ, ∫ t in Set.Ico (0 : ℝ) 1, g (s, t) = 0 := by
    intro s
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF s t)
        ((hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
    have := hper s 0
    simp only [zero_add] at this
    rw [this, sub_self]
  simp [h]

lemma integrable_of_vanish (g : ℝ × ℝ → ℝ) (hg : Continuous g) (R : ℝ)
    (hgR : ∀ s t, R < |s| → g (s, t) = 0) : Integrable g cylMeasure := by
  rw [← memLp_one_iff_integrable]
  exact memLp_of_vanish g hg R hgR

end LAPC

end

end CauchyRiemannIndex

/-!
# Large antilinear perturbations: the `L²` estimate on test sections

For `D_σ = ∂ₛ + J₀ ∂ₜ + S + σ A(β)` with `A(β) = antilinearMat β`, on a set `Ω` where `S = 0`,
`∂ₛβ = 1` and `∂ₜβ = -i`, and with `|β| ≥ c₀` off `Ω`:
`∫ |u|² ≤ (K / σ) ∫ |D_σ u|²` for test sections `u` and large `σ`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace LAPC

/-- `∂ₛβ`. -/
abbrev bS (β : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := fderiv ℝ β x (1, 0)
/-- `∂ₜβ`. -/
abbrev bT (β : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := fderiv ℝ β x (0, 1)

/-- The zeroth-order term of the cross term `2 ⟨D₀ u, A(β) u⟩`. -/
def crossQ (β : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Vec 1) (x : ℝ × ℝ) : ℝ :=
  ((bS β x).re + (bT β x).im) * (u x iq ^ 2 - u x ip ^ 2) +
    2 * ((bS β x).im - (bT β x).re) * (u x iq * u x ip)

/-- `D₀ u = ∂ₛ u + J₀ ∂ₜ u`. -/
abbrev D0 (u : ℝ × ℝ → Vec 1) (x : ℝ × ℝ) : Vec 1 :=
  partialS u x + Matrix.toEuclideanLin (J₀ 1) (partialT u x)

section

variable {β : ℝ × ℝ → ℂ} (hβ : ContDiff ℝ 1 β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
  {u : ℝ × ℝ → Vec 1} (hu : IsTestSection u)

include hβ in
lemma cont_bS : Continuous (bS β) :=
  (hβ.continuous_fderiv (by simp)).clm_apply continuous_const

include hβ in
lemma cont_bT : Continuous (bT β) :=
  (hβ.continuous_fderiv (by simp)).clm_apply continuous_const

include hu in
lemma cont_u (i : Fin 1 ⊕ Fin 1) : Continuous fun x => u x i :=
  continuous_comp_apply hu.continuous i

include hu in
lemma cont_uS (i : Fin 1 ⊕ Fin 1) : Continuous fun x => partialS u x i :=
  continuous_comp_apply hu.continuous_partialS i

include hu in
lemma cont_uT (i : Fin 1 ⊕ Fin 1) : Continuous fun x => partialT u x i :=
  continuous_comp_apply hu.continuous_partialT i

include hβ hu in
lemma cont_crossQ : Continuous (crossQ β u) := by
  have c1 := cont_bS hβ; have c2 := cont_bT hβ
  have u1 := cont_u hu iq; have u2 := cont_u hu ip
  have r1 : Continuous fun x => (bS β x).re := Complex.continuous_re.comp c1
  have r2 : Continuous fun x => (bS β x).im := Complex.continuous_im.comp c1
  have r3 : Continuous fun x => (bT β x).re := Complex.continuous_re.comp c2
  have r4 : Continuous fun x => (bT β x).im := Complex.continuous_im.comp c2
  exact ((r1.add r4).mul ((u1.pow 2).sub (u2.pow 2))).add
    ((continuous_const.mul (r2.sub r3)).mul (u1.mul u2))

include hβ hβper hu in
/-- `∫ ⟨D₀ u, A(β) u⟩ = -½ ∫ Q`. -/
lemma integral_cross :
    ∫ x, inner ℝ (D0 u x) (Matrix.toEuclideanLin (antilinearMat (β x)) (u x)) ∂cylMeasure =
      -(1 / 2) * ∫ x, crossQ β u x ∂cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
  have hβd : Differentiable ℝ β := hβ.differentiable (by simp)
  have cβ := hβ.continuous
  have cre : Continuous fun x => (β x).re := Complex.continuous_re.comp cβ
  have cim : Continuous fun x => (β x).im := Complex.continuous_im.comp cβ
  have c1 := cont_bS hβ; have c2 := cont_bT hβ
  have cbSr : Continuous fun x => (bS β x).re := Complex.continuous_re.comp c1
  have cbSi : Continuous fun x => (bS β x).im := Complex.continuous_im.comp c1
  have cbTr : Continuous fun x => (bT β x).re := Complex.continuous_re.comp c2
  have cbTi : Continuous fun x => (bT β x).im := Complex.continuous_im.comp c2
  have u1 := cont_u hu iq; have u2 := cont_u hu ip
  have a1 := cont_uS hu iq; have a2 := cont_uS hu ip
  have d1 := cont_uT hu iq; have d2 := cont_uT hu ip
  -- the two total derivatives
  set gS : ℝ × ℝ → ℝ := fun x => (bS β x).re * (u x iq ^ 2 - u x ip ^ 2) +
      (β x).re * (2 * u x iq * partialS u x iq - 2 * u x ip * partialS u x ip) +
      2 * (bS β x).im * (u x iq * u x ip) +
      2 * (β x).im * (partialS u x iq * u x ip + u x iq * partialS u x ip) with hgS
  set gT : ℝ × ℝ → ℝ := fun x => -(bT β x).im * (u x iq ^ 2 - u x ip ^ 2) -
      (β x).im * (2 * u x iq * partialT u x iq - 2 * u x ip * partialT u x ip) +
      2 * (bT β x).re * (u x iq * u x ip) +
      2 * (β x).re * (partialT u x iq * u x ip + u x iq * partialT u x ip) with hgT
  have hvan : ∀ s t, R < |s| → u (s, t) = 0 ∧ partialS u (s, t) = 0 ∧ partialT u (s, t) = 0 :=
    fun s t hs => ⟨hR s t hs, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs⟩
  have cgS : Continuous gS :=
    (((cbSr.mul ((u1.pow 2).sub (u2.pow 2))).add
      (cre.mul (((continuous_const.mul u1).mul a1).sub ((continuous_const.mul u2).mul a2)))).add
      ((continuous_const.mul cbSi).mul (u1.mul u2))).add
      ((continuous_const.mul cim).mul ((a1.mul u2).add (u1.mul a2)))
  have cgT : Continuous gT :=
    ((((cbTi.neg).mul ((u1.pow 2).sub (u2.pow 2))).sub
      (cim.mul (((continuous_const.mul u1).mul d1).sub ((continuous_const.mul u2).mul d2)))).add
      ((continuous_const.mul cbTr).mul (u1.mul u2))).add
      ((continuous_const.mul cre).mul ((d1.mul u2).add (u1.mul d2)))
  have igS : ∫ x, gS x ∂cylMeasure = 0 := by
    refine integral_s_eq_zero_of_hasDerivAt gS (fun x => (β x).re * (u x iq ^ 2 - u x ip ^ 2) +
      2 * (β x).im * (u x iq * u x ip)) cgS R ?_ ?_ ?_
    · intro s t hs; obtain ⟨h1, h2, -⟩ := hvan s t hs; simp [hgS, h1, h2]
    · intro s t hs; obtain ⟨h1, -, -⟩ := hvan s t hs; simp [h1]
    · intro s t
      have hb := hasDerivAt_s hβd s t
      have e1 := hasDerivAt_comp_apply (hasDerivAt_s hud s t) iq
      have e2 := hasDerivAt_comp_apply (hasDerivAt_s hud s t) ip
      have := (((hasDerivAt_re hb).mul ((e1.pow 2).sub (e2.pow 2))).add
        (((hasDerivAt_im hb).const_mul 2).mul (e1.mul e2)))
      refine this.congr_deriv ?_
      simp only [hgS, partialS, bS, Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
      ring
  have igT : ∫ x, gT x ∂cylMeasure = 0 := by
    refine integral_t_eq_zero_of_hasDerivAt gT (fun x => -(β x).im * (u x iq ^ 2 - u x ip ^ 2) +
      2 * (β x).re * (u x iq * u x ip)) cgT R ?_ ?_ ?_
    · intro s t hs; obtain ⟨h1, -, h3⟩ := hvan s t hs; simp [hgT, h1, h3]
    · intro s t; simp only [hβper, hu.2.1 s t]
    · intro s t
      have hb := hasDerivAt_t hβd s t
      have e1 := hasDerivAt_comp_apply (hasDerivAt_t hud s t) iq
      have e2 := hasDerivAt_comp_apply (hasDerivAt_t hud s t) ip
      have := ((((hasDerivAt_im hb).neg).mul ((e1.pow 2).sub (e2.pow 2))).add
        (((hasDerivAt_re hb).const_mul 2).mul (e1.mul e2)))
      refine this.congr_deriv ?_
      simp only [hgT, partialT, bT, Pi.neg_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
      ring
  have hpt : ∀ x, inner ℝ (D0 u x) (Matrix.toEuclideanLin (antilinearMat (β x)) (u x)) =
      (1 / 2) * gS x - (1 / 2) * gT x - (1 / 2) * crossQ β u x := by
    intro x
    simp only [D0, vec1_inner, add_apply', J_q, J_p, A_q, A_p, hgS, hgT, crossQ]
    ring
  have iS := integrable_of_vanish gS cgS R (fun s t hs => by
    obtain ⟨h1, h2, -⟩ := hvan s t hs; simp [hgS, h1, h2])
  have iT := integrable_of_vanish gT cgT R (fun s t hs => by
    obtain ⟨h1, -, h3⟩ := hvan s t hs; simp [hgT, h1, h3])
  have iQ := integrable_of_vanish (crossQ β u) (cont_crossQ hβ hu) R (fun s t hs => by
    obtain ⟨h1, -, -⟩ := hvan s t hs; simp [crossQ, h1])
  simp_rw [hpt]
  have j1 : Integrable (fun x => 1 / 2 * gS x) cylMeasure := iS.const_mul _
  have j2 : Integrable (fun x => 1 / 2 * gT x) cylMeasure := iT.const_mul _
  have j3 : Integrable (fun x => 1 / 2 * crossQ β u x) cylMeasure := iQ.const_mul _
  have j12 : Integrable (fun x => 1 / 2 * gS x - 1 / 2 * gT x) cylMeasure := j1.sub j2
  rw [integral_sub j12 j3, integral_sub j1 j2, integral_const_mul, integral_const_mul,
    integral_const_mul, igS, igT]
  ring

include hβ hu in
/-- `∫ (Re ∂ₛβ) |u|² = -2 ∫ (Re β) ⟨u, ∂ₛu⟩`. -/
lemma integral_ibp_re :
    ∫ x, (bS β x).re * ‖u x‖ ^ 2 ∂cylMeasure =
      -2 * ∫ x, (β x).re * inner ℝ (u x) (partialS u x) ∂cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
  have hβd : Differentiable ℝ β := hβ.differentiable (by simp)
  have cβ := hβ.continuous
  have cre : Continuous fun x => (β x).re := Complex.continuous_re.comp cβ
  have c1 := cont_bS hβ
  have cbSr : Continuous fun x => (bS β x).re := Complex.continuous_re.comp c1
  have u1 := cont_u hu iq; have u2 := cont_u hu ip
  have a1 := cont_uS hu iq; have a2 := cont_uS hu ip
  have hvan : ∀ s t, R < |s| → u (s, t) = 0 ∧ partialS u (s, t) = 0 :=
    fun s t hs => ⟨hR s t hs, partialS_eq_zero R hR hs⟩
  set g : ℝ × ℝ → ℝ := fun x => (bS β x).re * (u x iq ^ 2 + u x ip ^ 2) +
      (β x).re * (2 * u x iq * partialS u x iq + 2 * u x ip * partialS u x ip) with hg
  have cg : Continuous g :=
    (cbSr.mul ((u1.pow 2).add (u2.pow 2))).add
      (cre.mul (((continuous_const.mul u1).mul a1).add ((continuous_const.mul u2).mul a2)))
  have ig : ∫ x, g x ∂cylMeasure = 0 := by
    refine integral_s_eq_zero_of_hasDerivAt g (fun x => (β x).re * (u x iq ^ 2 + u x ip ^ 2))
      cg R ?_ ?_ ?_
    · intro s t hs; obtain ⟨h1, h2⟩ := hvan s t hs; simp [hg, h1, h2]
    · intro s t hs; obtain ⟨h1, -⟩ := hvan s t hs; simp [h1]
    · intro s t
      have hb := hasDerivAt_s hβd s t
      have e1 := hasDerivAt_comp_apply (hasDerivAt_s hud s t) iq
      have e2 := hasDerivAt_comp_apply (hasDerivAt_s hud s t) ip
      have := (hasDerivAt_re hb).mul ((e1.pow 2).add (e2.pow 2))
      refine this.congr_deriv ?_
      simp only [hg, partialS, bS, Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
      ring
  have h1 : ∀ x, (bS β x).re * ‖u x‖ ^ 2 =
      g x - 2 * ((β x).re * inner ℝ (u x) (partialS u x)) := by
    intro x; simp only [hg, vec1_norm_sq, vec1_inner]; ring
  have cI : Continuous fun x => (β x).re * inner ℝ (u x) (partialS u x) :=
    cre.mul (hu.continuous.inner hu.continuous_partialS)
  have iI := integrable_of_vanish _ cI R (fun s t hs => by
    obtain ⟨h1, -⟩ := hvan s t hs; simp [h1])
  have iG := integrable_of_vanish g cg R (fun s t hs => by
    obtain ⟨h1, h2⟩ := hvan s t hs; simp [hg, h1, h2])
  simp_rw [h1]
  have j2 : Integrable (fun x => 2 * ((β x).re * inner ℝ (u x) (partialS u x))) cylMeasure :=
    iI.const_mul _
  rw [integral_sub iG j2, integral_const_mul, ig]
  ring

end

end LAPC

end

end CauchyRiemannIndex

/-!
# Large antilinear perturbations: small helpers (norms, `A(β)`)
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace LAPC

lemma norm_prod_one_zero : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
lemma norm_prod_zero_one : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]

lemma norm_bS_le {β : ℝ × ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖fderiv ℝ β x‖ ≤ C) (x : ℝ × ℝ) :
    ‖bS β x‖ ≤ C :=
  ((fderiv ℝ β x).le_opNorm _).trans (by rw [norm_prod_one_zero, mul_one]; exact hC x)

lemma norm_bT_le {β : ℝ × ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖fderiv ℝ β x‖ ≤ C) (x : ℝ × ℝ) :
    ‖bT β x‖ ≤ C :=
  ((fderiv ℝ β x).le_opNorm _).trans (by rw [norm_prod_zero_one, mul_one]; exact hC x)

lemma toEL_add_smul (A Bm : Mat 1) (σ : ℝ) (v : Vec 1) :
    Matrix.toEuclideanLin (A + σ • Bm) v =
      Matrix.toEuclideanLin A v + σ • Matrix.toEuclideanLin Bm v := by
  rw [map_add, map_smul]; rfl

lemma continuous_antilinearMat_comp {β : ℝ × ℝ → ℂ} (hβ : Continuous β) :
    Continuous fun y => antilinearMat (β y) := by
  unfold antilinearMat
  refine Continuous.matrix_fromBlocks ?_ ?_ ?_ ?_ <;>
    refine continuous_pi fun _ => continuous_pi fun _ => ?_ <;>
    simp only [Matrix.of_apply] <;> fun_prop

end LAPC

end

end CauchyRiemannIndex

/-!
# Large antilinear perturbations: the `L²` estimate on test sections
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace LAPC

lemma abs_crossQ_le {β : ℝ × ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (u : ℝ × ℝ → Vec 1) (x : ℝ × ℝ) : |crossQ β u x| ≤ 4 * C * ‖u x‖ ^ 2 := by
  have h1 := norm_bS_le hC x; have h2 := norm_bT_le hC x
  have r1 := Complex.abs_re_le_norm (bS β x); have r2 := Complex.abs_im_le_norm (bS β x)
  have r3 := Complex.abs_re_le_norm (bT β x); have r4 := Complex.abs_im_le_norm (bT β x)
  have hA : |(bS β x).re + (bT β x).im| ≤ 2 * C := by
    have := abs_add_le (bS β x).re (bT β x).im; linarith
  have hB : |(bS β x).im - (bT β x).re| ≤ 2 * C := by
    have := abs_sub (bS β x).im (bT β x).re; linarith
  have hu := vec1_norm_sq (u x)
  have e1 : |u x iq ^ 2 - u x ip ^ 2| ≤ ‖u x‖ ^ 2 := by
    rw [hu, abs_le]; constructor <;> nlinarith [sq_nonneg (u x iq), sq_nonneg (u x ip)]
  have e2 : |2 * (u x iq * u x ip)| ≤ ‖u x‖ ^ 2 := by
    rw [hu, abs_le]; constructor <;> nlinarith [sq_nonneg (u x iq + u x ip),
      sq_nonneg (u x iq - u x ip)]
  unfold crossQ
  calc |((bS β x).re + (bT β x).im) * (u x iq ^ 2 - u x ip ^ 2) +
        2 * ((bS β x).im - (bT β x).re) * (u x iq * u x ip)|
      ≤ |(bS β x).re + (bT β x).im| * |u x iq ^ 2 - u x ip ^ 2| +
        |(bS β x).im - (bT β x).re| * |2 * (u x iq * u x ip)| := by
        have e : ((bS β x).re + (bT β x).im) * (u x iq ^ 2 - u x ip ^ 2) +
            2 * ((bS β x).im - (bT β x).re) * (u x iq * u x ip) =
            ((bS β x).re + (bT β x).im) * (u x iq ^ 2 - u x ip ^ 2) +
            ((bS β x).im - (bT β x).re) * (2 * (u x iq * u x ip)) := by ring
        rw [e, ← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ 2 * C * ‖u x‖ ^ 2 + 2 * C * ‖u x‖ ^ 2 := by
        gcongr <;> first | exact (abs_nonneg _) | positivity | skip
        all_goals linarith [abs_nonneg ((bS β x).re + (bT β x).im)]
    _ = 4 * C * ‖u x‖ ^ 2 := by ring

set_option maxHeartbeats 1000000 in
/-- The `L²` estimate for test sections. -/
theorem l2_estimate_test (S : ℝ × ℝ → Mat 1) (hSc : Continuous S) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x (v : Vec 1), ‖Matrix.toEuclideanLin (S x) v‖ ≤ B * ‖v‖)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ 1 β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (Ω : Set (ℝ × ℝ)) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hΩ : ∀ x ∈ Ω, S x = 0 ∧ bS β x = 1 ∧ bT β x = -Complex.I)
    (hoff : ∀ x ∉ Ω, c₀ ≤ ‖β x‖) :
    ∃ σ₀ K : ℝ, 1 ≤ σ₀ ∧ 0 < K ∧ ∀ σ ≥ σ₀, ∀ u, IsTestSection u →
      ∫ x, ‖u x‖ ^ 2 ∂cylMeasure ≤
        K / σ * ∫ x, ‖crOp (fun x => S x + σ • antilinearMat (β x)) u x‖ ^ 2 ∂cylMeasure := by
  set K₂ : ℝ := (1 + C) / c₀ ^ 2 with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hK₂c : K₂ * c₀ ^ 2 = 1 + C := by rw [hK₂]; field_simp
  refine ⟨max 1 ((20 * B ^ 2 + 16 * C) / c₀ ^ 2), 2 + 2 * K₂, le_max_left _ _, by positivity, ?_⟩
  intro σ hσ u hu
  have hσ1 : 1 ≤ σ := (le_max_left _ _).trans hσ
  have hσ0 : 0 < σ := by linarith
  have hσc : (20 * B ^ 2 + 16 * C) ≤ σ * c₀ ^ 2 := by
    have := (le_max_right _ _).trans hσ
    rwa [div_le_iff₀ (by positivity)] at this
  obtain ⟨R, hR⟩ := hu.2.2
  have hvan : ∀ s t, R < |s| → u (s, t) = 0 ∧ partialS u (s, t) = 0 ∧ partialT u (s, t) = 0 :=
    fun s t hs => ⟨hR s t hs, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs⟩
  -- notation
  set Au : ℝ × ℝ → Vec 1 := fun x => Matrix.toEuclideanLin (antilinearMat (β x)) (u x) with hAu
  set Su : ℝ × ℝ → Vec 1 := fun x => Matrix.toEuclideanLin (S x) (u x) with hSu
  have hD : ∀ x, crOp (fun x => S x + σ • antilinearMat (β x)) u x = D0 u x + Su x + σ • Au x := by
    intro x; simp only [crOp, toEL_add_smul, D0, hSu, hAu]; abel
  -- continuity
  have cβ := hβ.continuous
  have cAm : Continuous fun x => matCLM 1 (antilinearMat (β x)) := by
    refine continuous_matCLM.comp ?_
    unfold antilinearMat
    refine Continuous.matrix_fromBlocks ?_ ?_ ?_ ?_ <;>
      refine continuous_pi fun _ => continuous_pi fun _ => ?_ <;>
      simp only [Matrix.of_apply] <;> fun_prop
  have cAu : Continuous Au := cAm.clm_apply hu.continuous
  have cSu : Continuous Su := ((continuous_matCLM.comp hSc).clm_apply hu.continuous)
  have cD0 : Continuous (D0 u) :=
    hu.continuous_partialS.add ((matCLM 1 (J₀ 1)).continuous.comp hu.continuous_partialT)
  have cQ := cont_crossQ hβ hu
  have cnu : Continuous fun x => ‖u x‖ := hu.continuous.norm
  have cnb : Continuous fun x => ‖β x‖ := cβ.norm
  -- integrability
  have vD0 : ∀ s t, R < |s| → D0 u (s, t) = 0 := fun s t hs => by
    obtain ⟨-, h2, h3⟩ := hvan s t hs; simp [D0, h2, h3]
  have vSu : ∀ s t, R < |s| → Su (s, t) = 0 := fun s t hs => by
    obtain ⟨h1, -, -⟩ := hvan s t hs; simp [hSu, h1]
  have vAu : ∀ s t, R < |s| → Au (s, t) = 0 := fun s t hs => by
    obtain ⟨h1, -, -⟩ := hvan s t hs; simp [hAu, h1]
  have iI : ∀ g : ℝ × ℝ → ℝ, Continuous g → (∀ s t, R < |s| → g (s, t) = 0) →
      Integrable g cylMeasure := fun g hg hv => integrable_of_vanish g hg R hv
  -- main identity: ∫ |D u|² = ∫ F
  set F : ℝ × ℝ → ℝ := fun x => ‖D0 u x + Su x‖ ^ 2 + 2 * σ * inner ℝ (Su x) (Au x) +
      σ ^ 2 * ‖Au x‖ ^ 2 - σ * crossQ β u x with hF
  have hptD : ∀ x, ‖crOp (fun x => S x + σ • antilinearMat (β x)) u x‖ ^ 2 =
      F x + 2 * σ * (inner ℝ (D0 u x) (Au x) + (1 / 2) * crossQ β u x) := by
    intro x
    rw [hD, norm_add_sq_real, norm_smul, inner_smul_right, inner_add_left, Real.norm_eq_abs,
      abs_of_pos hσ0]
    simp only [hF]; ring
  have cF : Continuous F := by
    rw [hF]
    exact ((((cD0.add cSu).norm.pow 2).add (continuous_const.mul (cSu.inner cAu))).add
      (continuous_const.mul (cAu.norm.pow 2))).sub (continuous_const.mul cQ)
  have vF : ∀ s t, R < |s| → F (s, t) = 0 := fun s t hs => by
    have h1 := (hvan s t hs).1
    simp [hF, vD0 s t hs, vSu s t hs, vAu s t hs, crossQ, h1]
  have cX : Continuous fun x => inner ℝ (D0 u x) (Au x) := cD0.inner cAu
  have vX : ∀ s t, R < |s| → inner ℝ (D0 u (s, t)) (Au (s, t)) = 0 := fun s t hs => by
    simp [vD0 s t hs]
  have vQ : ∀ s t, R < |s| → crossQ β u (s, t) = 0 := fun s t hs => by
    simp [crossQ, (hvan s t hs).1]
  have hcross := integral_cross hβ hβper hu
  have hE : ∫ x, ‖crOp (fun x => S x + σ • antilinearMat (β x)) u x‖ ^ 2 ∂cylMeasure =
      ∫ x, F x ∂cylMeasure := by
    simp_rw [hptD]
    have j1 : Integrable (fun x => inner ℝ (D0 u x) (Au x)) cylMeasure := iI _ cX vX
    have j2 : Integrable (fun x => (1 / 2) * crossQ β u x) cylMeasure :=
      (iI _ cQ vQ).const_mul _
    have j3 : Integrable (fun x => 2 * σ * (inner ℝ (D0 u x) (Au x) + (1 / 2) * crossQ β u x))
      cylMeasure := (j1.add j2).const_mul _
    rw [integral_add (iI F cF vF) j3, integral_const_mul, integral_add j1 j2,
      integral_const_mul]
    have : ∫ x, inner ℝ (D0 u x) (Au x) ∂cylMeasure = -(1 / 2) * ∫ x, crossQ β u x ∂cylMeasure :=
      hcross
    rw [this]; ring
  -- pointwise lower bound for F
  have hFlow : ∀ x, (1 / 2) * ‖D0 u x‖ ^ 2 + (1 / 2) * σ ^ 2 * (‖β x‖ ^ 2 * ‖u x‖ ^ 2) ≤ F x := by
    intro x
    have hP : (1 / 2) * ‖D0 u x‖ ^ 2 - ‖Su x‖ ^ 2 ≤ ‖D0 u x + Su x‖ ^ 2 := by
      have h := norm_sub_le (D0 u x + Su x) (Su x)
      rw [add_sub_cancel_right] at h
      have h2 := mul_self_le_mul_self (norm_nonneg _) h
      nlinarith [sq_nonneg (‖D0 u x + Su x‖ - ‖Su x‖)]
    have hAn : ‖Au x‖ = ‖β x‖ * ‖u x‖ := norm_A _ _
    by_cases hx : x ∈ Ω
    · obtain ⟨h0, h1, h2⟩ := hΩ x hx
      have hS0 : Su x = 0 := by simp [hSu, h0]
      have hQ0 : crossQ β u x = 0 := by simp [crossQ, h1, h2]
      simp only [hF, hS0, hQ0, add_zero, inner_zero_left, mul_zero, sub_zero, hAn] at hP ⊢
      simp only [norm_zero] at hP
      nlinarith [sq_nonneg (‖β x‖ * ‖u x‖), sq_nonneg σ]
    · have hb := hoff x hx
      have hSn : ‖Su x‖ ≤ B * ‖u x‖ := hB x (u x)
      have hin : |inner ℝ (Su x) (Au x)| ≤ B * ‖u x‖ * (‖β x‖ * ‖u x‖) :=
        (abs_real_inner_le_norm _ _).trans (by rw [hAn]; gcongr)
      have hQ := abs_crossQ_le hC u x
      set a := ‖u x‖; set b := ‖β x‖
      have ha : 0 ≤ a := norm_nonneg _
      have hb0 : 0 ≤ b := norm_nonneg _
      have hS2 : ‖Su x‖ ^ 2 ≤ B ^ 2 * a ^ 2 := by
        have := norm_nonneg (Su x); nlinarith
      have hamgm : 2 * σ * B * b ≤ (1 / 4) * σ ^ 2 * b ^ 2 + 4 * B ^ 2 := by
        nlinarith [sq_nonneg (σ * b / 2 - 2 * B)]
      have hkey : 5 * B ^ 2 + 4 * σ * C ≤ (1 / 4) * σ ^ 2 * b ^ 2 := by
        have hbc : c₀ ^ 2 ≤ b ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hbc (by positivity : (0 : ℝ) ≤ σ ^ 2),
          mul_le_mul_of_nonneg_left hσc hσ0.le, sq_nonneg B]
      have hi := (abs_le.1 hin).1
      have hq := (abs_le.1 hQ).2
      simp only [hF, hAn]
      have e1 : 2 * σ * inner ℝ (Su x) (Au x) ≥ -(2 * σ * B * b) * a ^ 2 := by
        have := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ 2 * σ)
        linarith
      have e2 : σ * crossQ β u x ≤ 4 * σ * C * a ^ 2 := by
        have := mul_le_mul_of_nonneg_left hq hσ0.le
        linarith
      have e3 : (2 * σ * B * b) * a ^ 2 ≤ ((1 / 4) * σ ^ 2 * b ^ 2 + 4 * B ^ 2) * a ^ 2 :=
        mul_le_mul_of_nonneg_right hamgm (sq_nonneg a)
      have e4 : (5 * B ^ 2 + 4 * σ * C) * a ^ 2 ≤ ((1 / 4) * σ ^ 2 * b ^ 2) * a ^ 2 :=
        mul_le_mul_of_nonneg_right hkey (sq_nonneg a)
      linarith
  -- energy identity: ∫ |D₀ u|² ≥ ∫ |∂ₛ u|²
  have hen := crOp_energy_identity 1 (fun _ => 0) continuous_const
    (fun _ => Matrix.isSymm_zero) u hu
  have hD0eq : ∀ x, crOp (fun x : ℝ × ℝ => (fun _ : ℝ => (0 : Mat 1)) x.2) u x = D0 u x := by
    intro x; simp [crOp, D0]
  simp_rw [hD0eq] at hen
  have hX0 : 0 ≤ ∫ x, ‖Matrix.toEuclideanLin (J₀ 1) (partialT u x) +
      Matrix.toEuclideanLin ((fun _ : ℝ => (0 : Mat 1)) x.2) (u x)‖ ^ 2 ∂cylMeasure :=
    integral_nonneg fun _ => by positivity
  -- integrals
  set X := ∫ x, ‖partialS u x‖ ^ 2 ∂cylMeasure
  set Y := ∫ x, ‖β x‖ ^ 2 * ‖u x‖ ^ 2 ∂cylMeasure
  set E := ∫ x, ‖crOp (fun x => S x + σ • antilinearMat (β x)) u x‖ ^ 2 ∂cylMeasure
  have cD02 : Continuous fun x => ‖D0 u x‖ ^ 2 := cD0.norm.pow 2
  have vD02 : ∀ s t, R < |s| → ‖D0 u (s, t)‖ ^ 2 = 0 := fun s t hs => by simp [vD0 s t hs]
  have cY : Continuous fun x => ‖β x‖ ^ 2 * ‖u x‖ ^ 2 := (cnb.pow 2).mul (cnu.pow 2)
  have vY : ∀ s t, R < |s| → ‖β (s, t)‖ ^ 2 * ‖u (s, t)‖ ^ 2 = 0 := fun s t hs => by
    simp [(hvan s t hs).1]
  have hEXY : (1 / 2) * X + (1 / 2) * σ ^ 2 * Y ≤ E := by
    rw [hE]
    have j1 : Integrable (fun x => (1 / 2) * ‖D0 u x‖ ^ 2) cylMeasure :=
      (iI _ cD02 vD02).const_mul _
    have j2 : Integrable (fun x => (1 / 2) * σ ^ 2 * (‖β x‖ ^ 2 * ‖u x‖ ^ 2)) cylMeasure :=
      (iI _ cY vY).const_mul _
    have := integral_mono (j1.add j2) (iI F cF vF) hFlow
    simp only [Pi.add_apply] at this
    rw [integral_add j1 j2, integral_const_mul, integral_const_mul, hen] at this
    nlinarith
  -- the s-integration by parts
  have hibp := integral_ibp_re hβ hu
  have cbSr : Continuous fun x => (bS β x).re := Complex.continuous_re.comp (cont_bS hβ)
  have cre : Continuous fun x => (β x).re := Complex.continuous_re.comp cβ
  have cW : Continuous fun x => (bS β x).re * ‖u x‖ ^ 2 := cbSr.mul (cnu.pow 2)
  have vW : ∀ s t, R < |s| → (bS β (s, t)).re * ‖u (s, t)‖ ^ 2 = 0 := fun s t hs => by
    simp [(hvan s t hs).1]
  have cU : Continuous fun x => ‖u x‖ ^ 2 := cnu.pow 2
  have vU : ∀ s t, R < |s| → ‖u (s, t)‖ ^ 2 = 0 := fun s t hs => by simp [(hvan s t hs).1]
  have cS2 : Continuous fun x => ‖partialS u x‖ ^ 2 := hu.continuous_partialS.norm.pow 2
  have vS2 : ∀ s t, R < |s| → ‖partialS u (s, t)‖ ^ 2 = 0 := fun s t hs => by
    simp [(hvan s t hs).2.1]
  have cV : Continuous fun x => (β x).re * inner ℝ (u x) (partialS u x) :=
    cre.mul (hu.continuous.inner hu.continuous_partialS)
  have vV : ∀ s t, R < |s| → (β (s, t)).re * inner ℝ (u (s, t)) (partialS u (s, t)) = 0 :=
    fun s t hs => by simp [(hvan s t hs).1]
  have hU1 : ∫ x, ‖u x‖ ^ 2 ∂cylMeasure ≤
      ∫ x, (bS β x).re * ‖u x‖ ^ 2 ∂cylMeasure + K₂ * Y := by
    rw [← integral_const_mul, ← integral_add (iI _ cW vW) ((iI _ cY vY).const_mul _)]
    refine integral_mono (iI _ cU vU) ((iI _ cW vW).add ((iI _ cY vY).const_mul _)) fun x => ?_
    have hu2 : 0 ≤ ‖u x‖ ^ 2 := by positivity
    by_cases hx : x ∈ Ω
    · obtain ⟨-, h1, -⟩ := hΩ x hx
      simp only [h1, Complex.one_re, one_mul]
      have : 0 ≤ K₂ * (‖β x‖ ^ 2 * ‖u x‖ ^ 2) := by positivity
      linarith
    · have hb := hoff x hx
      have hre : -C ≤ (bS β x).re := by
        have := (abs_le.1 ((Complex.abs_re_le_norm _).trans (norm_bS_le hC x))).1; linarith
      have hb2 : c₀ ^ 2 ≤ ‖β x‖ ^ 2 := by nlinarith
      have : (1 + C) ≤ K₂ * ‖β x‖ ^ 2 := by
        rw [← hK₂c]; exact mul_le_mul_of_nonneg_left hb2 hK₂0
      nlinarith
  have hU2 : -2 * ∫ x, (β x).re * inner ℝ (u x) (partialS u x) ∂cylMeasure ≤
      σ * Y + σ⁻¹ * X := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add ((iI _ cY vY).const_mul _) ((iI _ cS2 vS2).const_mul _)]
    refine integral_mono ((iI _ cV vV).const_mul _) (((iI _ cY vY).const_mul _).add
      ((iI _ cS2 vS2).const_mul _)) fun x => ?_
    have h1 : |(β x).re * inner ℝ (u x) (partialS u x)| ≤ ‖β x‖ * (‖u x‖ * ‖partialS u x‖) := by
      rw [abs_mul]
      exact mul_le_mul (Complex.abs_re_le_norm _) (abs_real_inner_le_norm _ _)
        (abs_nonneg _) (norm_nonneg _)
    have h2 := (abs_le.1 h1).1
    set a := ‖β x‖ * ‖u x‖
    set b := ‖partialS u x‖
    have hab : 2 * (‖β x‖ * (‖u x‖ * b)) ≤ σ * a ^ 2 + σ⁻¹ * b ^ 2 := by
      have hs : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ0.ne'
      have : 0 ≤ σ⁻¹ * (σ * a - b) ^ 2 := by positivity
      have e : σ⁻¹ * (σ * a - b) ^ 2 = σ * a ^ 2 - 2 * a * b + σ⁻¹ * b ^ 2 := by
        field_simp; ring
      have e2 : ‖β x‖ * (‖u x‖ * b) = a * b := by simp only [a]; ring
      rw [e2]; linarith
    have e3 : ‖β x‖ ^ 2 * ‖u x‖ ^ 2 = a ^ 2 := by simp only [a]; ring
    rw [e3]
    linarith
  have hX0' : 0 ≤ X := integral_nonneg fun _ => by positivity
  have hY0 : 0 ≤ Y := integral_nonneg fun _ => by positivity
  -- combine
  have hfin : ∫ x, ‖u x‖ ^ 2 ∂cylMeasure ≤ σ * Y + σ⁻¹ * X + K₂ * Y := by
    rw [hibp] at hU1; linarith
  have hσi : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ0.ne'
  have g1 : σ * Y + σ⁻¹ * X ≤ 2 / σ * E := by
    have : σ * Y + σ⁻¹ * X = 2 / σ * ((1 / 2) * X + (1 / 2) * σ ^ 2 * Y) := by
      field_simp; ring
    rw [this]; exact mul_le_mul_of_nonneg_left hEXY (by positivity)
  have g2 : K₂ * Y ≤ 2 * K₂ / σ * E := by
    have hY : Y ≤ 2 / σ ^ 2 * E := by
      have : (1 / 2) * σ ^ 2 * Y ≤ E := by linarith
      calc Y = 2 / σ ^ 2 * ((1 / 2) * σ ^ 2 * Y) := by field_simp
        _ ≤ 2 / σ ^ 2 * E := mul_le_mul_of_nonneg_left this (by positivity)
    have hE0 : 0 ≤ E := integral_nonneg fun _ => by positivity
    calc K₂ * Y ≤ K₂ * (2 / σ ^ 2 * E) := mul_le_mul_of_nonneg_left hY hK₂0
      _ ≤ 2 * K₂ / σ * E := by
        have : 2 / σ ^ 2 ≤ 2 / σ := by
          apply div_le_div_of_nonneg_left (by norm_num) hσ0; nlinarith
        have := mul_le_mul_of_nonneg_right this hE0
        calc K₂ * (2 / σ ^ 2 * E) ≤ K₂ * (2 / σ * E) := mul_le_mul_of_nonneg_left this hK₂0
          _ = 2 * K₂ / σ * E := by ring
  calc ∫ x, ‖u x‖ ^ 2 ∂cylMeasure ≤ 2 / σ * E + 2 * K₂ / σ * E := by linarith
    _ = (2 + 2 * K₂) / σ * E := by ring

end LAPC

end

end CauchyRiemannIndex

/-!
# Large antilinear perturbations: from test sections to `W^{1,2}`
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace LAPC

variable {n : ℕ}

/-- A closed set containing the test triples contains `W^{1,p}`. -/
lemma w1p_subset_of_closed {p : ℝ≥0∞} [Fact (1 ≤ p)] {P : Set (Triple n p)}
    (hP : IsClosed P) (htest : ∀ w ∈ testTriples n p, w ∈ P) : ∀ w ∈ W1p p n, w ∈ P := by
  intro w hw
  have hsub : (W1p p n : Set (Triple n p)) ⊆ P := by
    unfold W1p
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal (fun w hw => htest w (span_testTriples_subset hw)) hP
  exact hsub hw

lemma L2_norm_sq_eq {f : LpCyl n 2} {g : ℝ × ℝ → Vec n} (h : (f : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g) :
    ‖f‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂cylMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

lemma L2_inner_eq {f f' : LpCyl n 2} {g g' : ℝ × ℝ → Vec n}
    (h : (f : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g) (h' : (f' : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g') :
    inner ℝ f f' = ∫ x, inner ℝ (g x) (g' x) ∂cylMeasure := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h, h'] with x hx hx'
  rw [hx, hx']

variable (T : ℝ × ℝ → Mat n) (hT : Continuous T)
  (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (T x) v‖ ≤ M * ‖v‖)

/-- The estimate on `W^{1,2}`. -/
lemma estimate_W1p (c : ℝ)
    (hest : ∀ u, IsTestSection u →
      ∫ x, ‖u x‖ ^ 2 ∂cylMeasure ≤ c * ∫ x, ‖crOp T u x‖ ^ 2 ∂cylMeasure) :
    ∀ w ∈ W1p 2 n, ‖w.1‖ ^ 2 ≤ c * ‖crsT (p := 2) T hT hb w‖ ^ 2 := by
  refine w1p_subset_of_closed (P := {w | ‖w.1‖ ^ 2 ≤ c * ‖crsT (p := 2) T hT hb w‖ ^ 2}) ?_ ?_
  · exact isClosed_le (continuous_fst.norm.pow 2)
      (continuous_const.mul ((crsT (p := 2) T hT hb).continuous.norm.pow 2))
  · rintro w ⟨u, hu, h1, h2, h3⟩
    simp only [Set.mem_setOf_eq]
    rw [L2_norm_sq_eq h1, L2_norm_sq_eq ((crsT_ae T hT hb w).trans (crApply_ae_crOp T h1 h2 h3))]
    exact hest u hu

/-- The formal adjoint `D*v = -∂ₛv + J₀ ∂ₜv + Tᵀ v`. -/
def adj (v : ℝ × ℝ → Vec n) (x : ℝ × ℝ) : Vec n :=
  -partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x) + Matrix.toEuclideanLin (T x)ᵀ (v x)

include hT in
lemma continuous_adj {v : ℝ × ℝ → Vec n} (hv : IsTestSection v) : Continuous (adj T v) := by
  have cT : Continuous fun x => matCLM n (T x)ᵀ :=
    continuous_matCLM.comp (hT.matrix_transpose)
  exact (hv.continuous_partialS.neg.add
    ((matCLM n (J₀ n)).continuous.comp hv.continuous_partialT)).add (cT.clm_apply hv.continuous)

include hT in
lemma memLp_adj {v : ℝ × ℝ → Vec n} (hv : IsTestSection v) : MemLp (adj T v) 2 cylMeasure := by
  obtain ⟨R, hR⟩ := hv.2.2
  refine memLp_of_vanish _ (continuous_adj T hT hv) R fun s t hs => ?_
  simp [adj, hR s t hs, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs]

/-- `⟨v, D w⟩ = ⟨D* v, w⟩` on `W^{1,2}`. -/
lemma adjoint_W1p {v : ℝ × ℝ → Vec n} (hv : IsTestSection v) :
    ∀ w ∈ W1p 2 n, inner ℝ ((hv.memLp (p := 2)).toLp v) (crsT (p := 2) T hT hb w) =
      inner ℝ ((memLp_adj T hT hv).toLp (adj T v)) w.1 := by
  refine w1p_subset_of_closed
    (P := {w | inner ℝ ((hv.memLp (p := 2)).toLp v) (crsT (p := 2) T hT hb w) =
      inner ℝ ((memLp_adj T hT hv).toLp (adj T v)) w.1}) ?_ ?_
  · exact isClosed_eq (continuous_const.inner (crsT (p := 2) T hT hb).continuous)
      (continuous_const.inner continuous_fst)
  · rintro w ⟨u, hu, h1, h2, h3⟩
    simp only [Set.mem_setOf_eq]
    rw [L2_inner_eq (hv.memLp (p := 2)).coeFn_toLp
        ((crsT_ae T hT hb w).trans (crApply_ae_crOp T h1 h2 h3)),
      L2_inner_eq (memLp_adj T hT hv).coeFn_toLp h1]
    have := crOp_formalAdjoint n T hT u v hu hv
    calc ∫ x, inner ℝ (v x) (crOp T u x) ∂cylMeasure
        = ∫ x, inner ℝ (crOp T u x) (v x) ∂cylMeasure :=
          integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)
      _ = _ := this
      _ = ∫ x, inner ℝ (adj T v x) (u x) ∂cylMeasure :=
          integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)

end LAPC

end

end CauchyRiemannIndex

/-!
# Large antilinear perturbations: the geometry of the zeros
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace LAPC

lemma per_int {β : Type*} {F : ℝ × ℝ → β} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (s t : ℝ)
    (m : ℤ) : F (s, t + m) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hF s t
  have := (hp.int_mul m) t
  simpa using this

/-- The complex number `(x₁ - a₁) + i (x₂ - a₂ - m)`. -/
def zc (a : ℝ × ℝ) (m : ℤ) (x : ℝ × ℝ) : ℂ := ⟨x.1 - a.1, x.2 - a.2 - m⟩

lemma continuous_zc (a : ℝ × ℝ) (m : ℤ) : Continuous (zc a m) := by
  have h : zc a m = fun x => ((x.1 - a.1 : ℝ) : ℂ) + ((x.2 - a.2 - m : ℝ) : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp [zc]
  rw [h]; fun_prop

lemma eq_zc (a : ℝ × ℝ) (m : ℤ) (x : ℝ × ℝ) :
    x = (a.1 + (zc a m x).re, a.2 + (zc a m x).im + m) := by
  ext <;> simp [zc] <;> ring

/-- The discs of radius `r` around the periodic copies of the points of `Z`. -/
def discs (Z : Finset (ℝ × ℝ)) (r : ℝ) : Set (ℝ × ℝ) :=
  ⋃ ζ ∈ Z, ⋃ m : ℤ, {x | ‖zc ζ m x‖ < r}

lemma isOpen_discs (Z : Finset (ℝ × ℝ)) (r : ℝ) : IsOpen (discs Z r) :=
  isOpen_biUnion fun ζ _ => isOpen_iUnion fun m =>
    isOpen_lt (continuous_zc ζ m).norm continuous_const

lemma mem_discs {Z : Finset (ℝ × ℝ)} {r : ℝ} {x : ℝ × ℝ} :
    x ∈ discs Z r ↔ ∃ ζ ∈ Z, ∃ m : ℤ, ‖zc ζ m x‖ < r := by
  simp [discs]

lemma discs_shift {Z : Finset (ℝ × ℝ)} {r : ℝ} {s t : ℝ} (k : ℤ)
    (h : (s, t + k) ∈ discs Z r) : (s, t) ∈ discs Z r := by
  obtain ⟨ζ, hζ, m, hm⟩ := mem_discs.1 h
  refine mem_discs.2 ⟨ζ, hζ, m - k, ?_⟩
  convert hm using 2
  apply Complex.ext <;> simp [zc] <;> ring

/-- Slice derivatives of `β` from a local formula. -/
lemma bS_bT_of_local {β : ℝ × ℝ → ℂ} (hβ : Differentiable ℝ β) {x : ℝ × ℝ} {g : ℝ × ℝ → ℂ}
    (hloc : β =ᶠ[𝓝 x] g) {gs gt : ℂ}
    (hs : HasDerivAt (fun s => g (s, x.2)) gs x.1) (ht : HasDerivAt (fun t => g (x.1, t)) gt x.2) :
    bS β x = gs ∧ bT β x = gt := by
  have c1 : Continuous fun s : ℝ => (s, x.2) := continuous_id.prodMk continuous_const
  have c2 : Continuous fun t : ℝ => (x.1, t) := continuous_const.prodMk continuous_id
  have h1 : (fun s => β (s, x.2)) =ᶠ[𝓝 x.1] fun s => g (s, x.2) :=
    hloc.comp_tendsto (c1.tendsto x.1)
  have h2 : (fun t => β (x.1, t)) =ᶠ[𝓝 x.2] fun t => g (x.1, t) :=
    hloc.comp_tendsto (c2.tendsto x.2)
  refine ⟨(hasDerivAt_s hβ x.1 x.2).unique (hs.congr_of_eventuallyEq h1), ?_⟩
  exact (hasDerivAt_t hβ x.1 x.2).unique (ht.congr_of_eventuallyEq h2)

variable (S : ℝ × ℝ → Mat 1) (hSper : ∀ s t, S (s, t + 1) = S (s, t))
  (β : ℝ × ℝ → ℂ) (hβd : Differentiable ℝ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
  (Zminus : Finset (ℝ × ℝ)) (r : ℝ)
  (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)

include hSper hβper hminusZ in
/-- On a disc around a copy of a negative zero, `β = z̄` and `S = 0`. -/
lemma local_formula {ζ : ℝ × ℝ} (hζ : ζ ∈ Zminus) (m : ℤ) {y : ℝ × ℝ} (hy : ‖zc ζ m y‖ < r) :
    β y = (starRingEnd ℂ) (zc ζ m y) ∧ S y = 0 := by
  have e := eq_zc ζ m y
  obtain ⟨h1, h2⟩ := hminusZ ζ hζ (zc ζ m y) hy
  exact ⟨(congrArg β e).trans ((per_int hβper _ _ m).trans h1),
    (congrArg S e).trans ((per_int hSper _ _ m).trans h2)⟩

include hSper hβd hβper hminusZ in
lemma on_discs : ∀ x ∈ discs Zminus r, S x = 0 ∧ bS β x = 1 ∧ bT β x = -Complex.I := by
  intro x hx
  obtain ⟨ζ, hζ, m, hm⟩ := mem_discs.1 hx
  have hopen : {y | ‖zc ζ m y‖ < r} ∈ 𝓝 x :=
    (isOpen_lt (continuous_zc ζ m).norm continuous_const).mem_nhds hm
  have hloc : β =ᶠ[𝓝 x] fun y => (starRingEnd ℂ) (zc ζ m y) :=
    Filter.eventually_of_mem hopen fun y hy => (local_formula S hSper β hβper Zminus r hminusZ hζ m hy).1
  have hg : (fun y => (starRingEnd ℂ) (zc ζ m y)) =
      fun y : ℝ × ℝ => ((y.1 - ζ.1 : ℝ) : ℂ) - ((y.2 - ζ.2 - m : ℝ) : ℂ) * Complex.I := by
    funext y; apply Complex.ext <;> simp [zc]
  rw [hg] at hloc
  have hs : HasDerivAt (fun s : ℝ => ((s - ζ.1 : ℝ) : ℂ) - ((x.2 - ζ.2 - m : ℝ) : ℂ) * Complex.I)
      1 x.1 := by
    have := ((hasDerivAt_id x.1).sub_const ζ.1).ofReal_comp
    simpa using this.sub_const (((x.2 - ζ.2 - m : ℝ) : ℂ) * Complex.I)
  have ht : HasDerivAt (fun t : ℝ => ((x.1 - ζ.1 : ℝ) : ℂ) - ((t - ζ.2 - m : ℝ) : ℂ) * Complex.I)
      (-Complex.I) x.2 := by
    have := ((((hasDerivAt_id x.2).sub_const ζ.2).sub_const (m : ℝ)).ofReal_comp).mul_const
      Complex.I
    simpa using this.const_sub (((x.1 - ζ.1 : ℝ) : ℂ))
  obtain ⟨e1, e2⟩ := bS_bT_of_local hβd hloc hs ht
  exact ⟨(local_formula S hSper β hβper Zminus r hminusZ hζ m hm).2, e1, e2⟩

/-- Periodic functions bounded on the slab and for large `|s|` are bounded. -/
lemma bound_of_periodic {f : ℝ × ℝ → ℝ} (hf : Continuous f) (hper : ∀ s t, f (s, t + 1) = f (s, t))
    {R M : ℝ} (hR : ∀ s t, R ≤ |s| → f (s, t) ≤ M) : ∃ M' : ℝ, ∀ x, f x ≤ M' := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hf.continuousOn
  refine ⟨max C M, fun x => ?_⟩
  by_cases h : R ≤ |x.1|
  · exact (hR x.1 x.2 h).trans (le_max_right _ _)
  · push_neg at h
    have hx : (x.1, Int.fract x.2) ∈ Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1 := by
      refine Set.mk_mem_prod ?_ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
      have := le_abs_self R
      exact abs_le.1 (by linarith)
    have e : f (x.1, Int.fract x.2) = f x := crs_per hper x.1 x.2
    have h1 : f (x.1, Int.fract x.2) ≤ C :=
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC _ hx)
    rw [e] at h1
    exact h1.trans (le_max_left _ _)

include hβper in
lemma beta_bound (hβc : Continuous β)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖β x‖ ≤ M := by
  obtain ⟨R, c, -, hc⟩ := hβends
  obtain ⟨M, hM⟩ := bound_of_periodic (f := fun x => ‖β x‖) hβc.norm
    (fun s t => by simp only [hβper]) (R := R) (M := 1 / c) fun s t h => (hc s t h).2
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩

include hSper hβper hminusZ in
lemma off_discs (hβc : Continuous β) (hr : 0 < r) (Zplus : Finset (ℝ × ℝ))
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (hZplus : Zplus = ∅)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x ∉ discs Zminus r, c₀ ≤ ‖β x‖ := by
  obtain ⟨R, c, hc0, hc⟩ := hβends
  set K : Set (ℝ × ℝ) := (Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1) \ discs Zminus r with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).diff (isOpen_discs Zminus r)
  have hpos : ∀ x ∈ K, 0 < ‖β x‖ := by
    intro x hx
    refine norm_pos_iff.2 fun h0 => hx.2 ?_
    obtain ⟨ζ, hζ, m, rfl⟩ := (hzero x).1 h0
    rw [hZplus, Finset.empty_union] at hζ
    refine mem_discs.2 ⟨ζ, hζ, m, ?_⟩
    rw [show zc ζ m (ζ.1, ζ.2 + m) = 0 from Complex.ext (by simp [zc]) (by simp [zc])]
    simpa using hr
  have hmin : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ x ∈ K, c₁ ≤ ‖β x‖ := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun x hx => by simp [he] at hx⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hne hβc.norm.continuousOn
      exact ⟨‖β x₀‖, hpos x₀ hx₀, fun x hx => hmin hx⟩
  obtain ⟨c₁, hc₁, hK1⟩ := hmin
  refine ⟨min c c₁, lt_min hc0 hc₁, fun x hx => ?_⟩
  by_cases h : R ≤ |x.1|
  · exact (min_le_left _ _).trans (hc x.1 x.2 h).1
  · push_neg at h
    have hx' : (x.1, Int.fract x.2) ∈ K := by
      refine ⟨Set.mk_mem_prod ?_ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, fun hm => hx ?_⟩
      · have := le_abs_self R
        exact abs_le.1 (by linarith)
      · have e : x.2 + ((-⌊x.2⌋ : ℤ) : ℝ) = Int.fract x.2 := by
          rw [Int.fract]; push_cast; ring
        apply discs_shift (-⌊x.2⌋)
        rw [e]; exact hm
    have e : β (x.1, Int.fract x.2) = β x := crs_per hβper x.1 x.2
    exact (min_le_right _ _).trans (e ▸ hK1 _ hx')

end LAPC

end

end CauchyRiemannIndex

/-!
# A lower bound for the cokernel of `D_T` from approximate solutions of the adjoint equation

If `‖η‖² ≤ c ‖D_T η‖²` on `W^{1,2}` and `v = Σ gᵢ vᵢ ∈ im D_T`, say `v = D_T w`, then
`‖v‖² = ⟨v, D_T w⟩ = ⟨D_T* v, w⟩ ≤ ‖D_T* v‖ √c ‖v‖`, so `‖v‖² ≤ c ‖D_T* v‖²`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace LAPC

variable {n : ℕ}

lemma coeFn_sum_smul {ι : Type*} (s : Finset ι) (g : ι → ℝ) (F : ι → LpCyl n 2)
    (f : ι → ℝ × ℝ → Vec n) (hF : ∀ i, (F i : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] f i) :
    ((∑ i ∈ s, g i • F i : LpCyl n 2) : ℝ × ℝ → Vec n) =ᵐ[cylMeasure]
      fun x => ∑ i ∈ s, g i • f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (g a • F a) (∑ i ∈ s, g i • F i), Lp.coeFn_smul (g a) (F a),
      hF a, ih] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]

/-- Every element of the range is `D w` for some `w ∈ W^{1,2}`. -/
lemma mem_range_crsT (T : ℝ × ℝ → Mat n) (hT : Continuous T)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (T x) v‖ ≤ M * ‖v‖)
    {f : LpCyl n 2} (hf : f ∈ crRange 2 T) : ∃ w ∈ W1p 2 n, f = crsT (p := 2) T hT hb w := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w, hw, hfw⟩ := hf
    exact ⟨w, hw, Lp.ext (hfw.trans (crsT_ae T hT hb w).symm)⟩
  | zero => exact ⟨0, (W1p 2 n).zero_mem, by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨w, hw, rfl⟩ := hf
    obtain ⟨w', hw', rfl⟩ := hg
    exact ⟨w + w', (W1p 2 n).add_mem hw hw', by simp⟩
  | smul c f _ hf =>
    obtain ⟨w, hw, rfl⟩ := hf
    exact ⟨c • w, (W1p 2 n).smul_mem c hw, by simp⟩

lemma eLpNorm_eq_ofReal_norm (f : LpCyl n 2) :
    eLpNorm (f : ℝ × ℝ → Vec n) 2 cylMeasure = ENNReal.ofReal ‖f‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

theorem linearIndependent_cokernel_of_adjoint_small_aux (n : ℕ) (T : ℝ × ℝ → Mat n)
    (hT : Continuous T)
    (hTb : ∃ M : ℝ, ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (T x) v‖ ≤ M * ‖v‖)
    (c : ℝ) (hc : 0 ≤ c)
    (hest : ∀ w ∈ W1p 2 n, eLpNorm (w.1 : ℝ × ℝ → Vec n) 2 cylMeasure ^ 2 ≤
      ENNReal.ofReal c * eLpNorm (crApply T w) 2 cylMeasure ^ 2)
    (k : ℕ) (v : Fin k → ℝ × ℝ → Vec n) (hv : ∀ i, IsTestSection (v i))
    (hsmall : ∀ g : Fin k → ℝ, g ≠ 0 →
      c * ∫ x, ‖∑ i, g i • (-partialS (v i) x + Matrix.toEuclideanLin (J₀ n) (partialT (v i) x) +
        Matrix.toEuclideanLin (T x)ᵀ (v i x))‖ ^ 2 ∂cylMeasure <
      ∫ x, ‖∑ i, g i • v i x‖ ^ 2 ∂cylMeasure) :
    ∃ u : Fin k → LpCyl n 2 ⧸ crRange 2 T, LinearIndependent ℝ u := by
  classical
  obtain ⟨M, hM⟩ := hTb
  have hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (T x) v‖ ≤ M * ‖v‖ :=
    ⟨max M 0, le_max_right _ _, fun x w =>
      (hM x w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
  have hW : ∀ w ∈ W1p 2 n, ‖w.1‖ ^ 2 ≤ c * ‖crsT (p := 2) T hT hb w‖ ^ 2 := by
    intro w hw
    have h := hest w hw
    rw [← eLpNorm_congr_ae (crsT_ae T hT hb w), eLpNorm_eq_ofReal_norm,
      eLpNorm_eq_ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hc] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  set V : Fin k → LpCyl n 2 := fun i => ((hv i).memLp (p := 2)).toLp (v i)
  set W : Fin k → LpCyl n 2 := fun i => (memLp_adj T hT (hv i)).toLp (adj T (v i))
  refine ⟨fun i => Submodule.Quotient.mk (V i), ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨i₀, hi₀⟩ := hne
  have hg0 : g ≠ 0 := fun h => hi₀ (by simp [h])
  have hX : ∑ i, g i • V i ∈ crRange 2 T := by
    have : (crRange 2 T).mkQ (∑ i, g i • V i) = 0 := by
      rw [map_sum]; simpa using hg
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  obtain ⟨w, hw, hXw⟩ := mem_range_crsT T hT hb hX
  have hpair : inner ℝ (∑ i, g i • V i) (∑ i, g i • V i) = inner ℝ (∑ i, g i • W i) w.1 := by
    have e : inner ℝ (∑ i, g i • V i) (∑ i, g i • V i) =
        inner ℝ (∑ i, g i • V i) (crsT (p := 2) T hT hb w) := by rw [← hXw]
    rw [e, sum_inner, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, real_inner_smul_left, adjoint_W1p T hT hb (hv i) w hw]
  set X := ∑ i, g i • V i
  set Y := ∑ i, g i • W i
  have hw1 : ‖w.1‖ ^ 2 ≤ c * ‖X‖ ^ 2 := by
    have := hW w hw; rwa [← hXw] at this
  have hXY : ‖X‖ ^ 2 ≤ c * ‖Y‖ ^ 2 := by
    have h1 : ‖X‖ ^ 2 ≤ ‖Y‖ * ‖w.1‖ := by
      rw [← real_inner_self_eq_norm_sq, hpair]; exact real_inner_le_norm _ _
    have h2 : (‖X‖ ^ 2) ^ 2 ≤ ‖Y‖ ^ 2 * (c * ‖X‖ ^ 2) := by
      calc (‖X‖ ^ 2) ^ 2 ≤ (‖Y‖ * ‖w.1‖) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = ‖Y‖ ^ 2 * ‖w.1‖ ^ 2 := by ring
        _ ≤ ‖Y‖ ^ 2 * (c * ‖X‖ ^ 2) := mul_le_mul_of_nonneg_left hw1 (by positivity)
    rcases eq_or_lt_of_le (sq_nonneg ‖X‖) with h0 | h0
    · rw [← h0]; positivity
    · nlinarith
  have hXn : ‖X‖ ^ 2 = ∫ x, ‖∑ i, g i • v i x‖ ^ 2 ∂cylMeasure :=
    L2_norm_sq_eq (coeFn_sum_smul Finset.univ g V v fun i => MemLp.coeFn_toLp _)
  have hYn : ‖Y‖ ^ 2 = ∫ x, ‖∑ i, g i • (-partialS (v i) x +
      Matrix.toEuclideanLin (J₀ n) (partialT (v i) x) +
        Matrix.toEuclideanLin (T x)ᵀ (v i x))‖ ^ 2 ∂cylMeasure :=
    L2_norm_sq_eq (coeFn_sum_smul Finset.univ g W (fun i => adj T (v i))
      fun i => MemLp.coeFn_toLp _)
  have := hsmall g hg0
  rw [← hXn, ← hYn] at this
  linarith

end LAPC

end

end CauchyRiemannIndex

/-!
# Large antilinear perturbations with negative zeros: the `L²` estimate on `W^{1,2}`
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace LAPC

theorem large_antilinear_l2_estimate_aux (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zminus : Finset (ℝ × ℝ))
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0) :
    ∃ σ₀ C : ℝ, 0 < σ₀ ∧ ∀ σ ≥ σ₀, ∀ w ∈ W1p 2 1,
      eLpNorm (w.1 : ℝ × ℝ → Vec 1) 2 cylMeasure ^ 2 ≤
        ENNReal.ofReal (C / σ) *
          eLpNorm (crApply (fun x => S x + σ • antilinearMat (β x)) w) 2 cylMeasure ^ 2 := by
  have hSper := hS.2.1
  have hβ1 : ContDiff ℝ 1 β := hβ.of_le (by simp)
  have hβd : Differentiable ℝ β := hβ.differentiable (by simp)
  obtain ⟨B, hB0, hB⟩ := crs_Sbound hSplus hSminus hS
  obtain ⟨C', hC'⟩ := hβC1
  have hzero' : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ (∅ : Finset (ℝ × ℝ)) ∪ Zminus, ∃ m : ℤ,
      x = (ζ.1, ζ.2 + m) := by
    intro x; rw [Finset.empty_union]; exact hzero x
  obtain ⟨c₀, hc₀, hoff⟩ :=
    off_discs S hSper β hβper Zminus r hminusZ hβ.continuous hr ∅ hzero' rfl hβends
  have hon := on_discs S hSper β hβd hβper Zminus r hminusZ
  obtain ⟨σ₁, K, hσ₁, hK, hest⟩ := l2_estimate_test S hS.1 B hB0 hB β hβ1 hβper (max C' 0)
    (le_max_right _ _) (fun x => (hC' x).trans (le_max_left _ _)) (discs Zminus r) c₀ hc₀ hon hoff
  obtain ⟨Mβ, hMβ0, hMβ⟩ := beta_bound β hβper hβ.continuous hβends
  refine ⟨σ₁, K, by linarith, fun σ hσ w hw => ?_⟩
  have hσ0 : 0 < σ := by linarith
  set T : ℝ × ℝ → Mat 1 := fun x => S x + σ • antilinearMat (β x) with hTdef
  have hTc : Continuous T := hS.1.add ((continuous_antilinearMat_comp hβ.continuous).const_smul σ)
  have hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec 1), ‖Matrix.toEuclideanLin (T x) v‖ ≤ M * ‖v‖ := by
    refine ⟨B + σ * Mβ, by positivity, fun x v => ?_⟩
    simp only [hTdef, toEL_add_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_A, Real.norm_eq_abs, abs_of_pos hσ0]
    have := hB x v
    have := mul_le_mul_of_nonneg_right (hMβ x) (norm_nonneg v)
    nlinarith [norm_nonneg v]
  have h := estimate_W1p T hTc hb (K / σ) (hest σ hσ) w hw
  rw [← eLpNorm_congr_ae (crsT_ae T hTc hb w), eLpNorm_eq_ofReal_norm, eLpNorm_eq_ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

end LAPC

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zminus : Finset (ℝ × ℝ))
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0) :
    ∃ σ₀ C : ℝ, 0 < σ₀ ∧ ∀ σ ≥ σ₀, ∀ w ∈ W1p 2 1,
      eLpNorm (w.1 : ℝ × ℝ → Vec 1) 2 cylMeasure ^ 2 ≤
        ENNReal.ofReal (C / σ) *
          eLpNorm (crApply (fun x => S x + σ • antilinearMat (β x)) w) 2 cylMeasure ^ 2 :=
  LAPC.large_antilinear_l2_estimate_aux Splus Sminus hSplus hSminus S hS β hβ hβper hβC1 hβends Zminus hzero r hr hminusZ
