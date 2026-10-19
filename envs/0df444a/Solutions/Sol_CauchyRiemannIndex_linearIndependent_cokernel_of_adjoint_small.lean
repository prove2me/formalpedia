-- Prove2me | solution 1 for CauchyRiemannIndex.linearIndependent_cokernel_of_adjoint_small
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:10:10.97165+00:00
-- url     : https://prove2.me/submissions/b15b1153-753c-4601-80ed-932af912b537

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Theorems.Thm_CauchyRiemannIndex_global_estimate
import Theorems.Thm_CauchyRiemannIndex_compact_restriction
import Theorems.Thm_CauchyRiemannIndex_finiteDimensional_ker_isClosed_range_of_estimate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Compact.Basic
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

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (T : ℝ × ℝ → Mat n)
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
    ∃ u : Fin k → LpCyl n 2 ⧸ crRange 2 T, LinearIndependent ℝ u :=
  LAPC.linearIndependent_cokernel_of_adjoint_small_aux n T hT hTb c hc hest k v hv hsmall
