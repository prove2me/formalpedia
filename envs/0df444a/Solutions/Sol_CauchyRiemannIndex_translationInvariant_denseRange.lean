-- Prove2me | solution 1 for CauchyRiemannIndex.translationInvariant_denseRange
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-13T23:17:04.212155+00:00
-- url     : https://prove2.me/submissions/adfbb485-cbd0-491e-adb9-1d47f30d10c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Theorems.Thm_CauchyRiemannIndex_memW1p_of_weak_solution
import Theorems.Thm_CauchyRiemannIndex_dense_of_forall_integral_inner_eq_zero
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_annihilator_eq_zero
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_Lp_bound
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_derivative_estimate
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
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### Kernel of `D` on `W^{1,p}` from an a priori bound -/

lemma eq_zero_of_crApply_eq_zero {p : ℝ≥0∞} [Fact (1 ≤ p)] (Sinf : ℝ → Mat n)
    (hS : IsSymLoop Sinf)
    (K1 : ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure)
    (w : Triple n p) (hw : w ∈ W1p p n)
    (h0 : crApply (fun x : ℝ × ℝ => Sinf x.2) w =ᵐ[cylMeasure] 0) : w = 0 := by
  set S : ℝ × ℝ → Mat n := fun x => Sinf x.2 with hSdef
  obtain ⟨M, hM0, hM⟩ := exists_bound_loop Sinf hS.1 hS.2.1
  obtain ⟨MJ, hMJ0, hMJ⟩ := exists_bound_mat (J₀ n)
  obtain ⟨c, hc⟩ := K1
  set A : ℝ := 1 + MJ + M with hA
  have hA0 : 0 ≤ A := by positivity
  have hLip : ∀ w w' : Triple n p, eLpNorm (crApply S w - crApply S w') p cylMeasure ≤
      ENNReal.ofReal A * ENNReal.ofReal ‖w - w'‖ := by
    intro w w'
    refine eLpNorm_le_of_pointwise hM0 hMJ0 ?_
    filter_upwards [crApply_sub_ae S w w'] with x hx
    have hx' : crApply S w x - crApply S w' x = crApply S (w - w') x := by rw [hx]; rfl
    rw [Pi.sub_apply, hx']
    calc ‖crApply S (w - w') x‖ ≤ ‖(w - w').2.1 x‖ + ‖Matrix.toEuclideanLin (J₀ n) ((w - w').2.2 x)‖
          + ‖Matrix.toEuclideanLin (S x) ((w - w').1 x)‖ := norm_add₃_le
      _ ≤ 1 * ‖(w - w').2.1 x‖ + MJ * ‖(w - w').2.2 x‖ + M * ‖(w - w').1 x‖ := by
          rw [one_mul]
          gcongr
          · exact hMJ _
          · exact hM _ _
  have hT : ∀ w ∈ testTriples n p, ENNReal.ofReal ‖w‖ ≤ c * eLpNorm (crApply S w) p cylMeasure := by
    rintro w ⟨u, hu, h1, h2, h3⟩
    rw [eLpNorm_congr_ae (crApply_ae_crOp S h1 h2 h3)]
    exact (ofReal_norm_le_w1pNorm h1 h2 h3).trans (hc u hu)
  have hcoe : (c : ℝ≥0∞) = ENNReal.ofReal c := (ENNReal.ofReal_coe_nnreal).symm
  have hW : w ∈ closure (testTriples n p) := by
    have : w ∈ ((Submodule.span ℝ (testTriples n p)).topologicalClosure : Set (Triple n p)) := hw
    rw [Submodule.topologicalClosure_coe] at this
    exact closure_mono span_testTriples_subset this
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
  obtain ⟨w', hw', hd⟩ := Metric.mem_closure_iff.1 hW (δ / (c * A + 1)) (by positivity)
  rw [dist_eq_norm] at hd
  have h1 : ENNReal.ofReal ‖w'‖ ≤ ENNReal.ofReal (c * A * ‖w' - w‖) := by
    have e : crApply S w' =ᵐ[cylMeasure] crApply S w' - crApply S w := by
      filter_upwards [h0] with x hx
      simp [hx]
    calc ENNReal.ofReal ‖w'‖ ≤ c * eLpNorm (crApply S w') p cylMeasure := hT w' hw'
      _ = c * eLpNorm (crApply S w' - crApply S w) p cylMeasure := by rw [eLpNorm_congr_ae e]
      _ ≤ c * (ENNReal.ofReal A * ENNReal.ofReal ‖w' - w‖) := by gcongr; exact hLip w' w
      _ = ENNReal.ofReal (c * A * ‖w' - w‖) := by
        rw [hcoe, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          mul_assoc]
  have h2 : ‖w'‖ ≤ c * A * ‖w' - w‖ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have h3 : ‖w' - w‖ = ‖w - w'‖ := norm_sub_rev _ _
  have h4 : (c * A + 1) * ‖w - w'‖ ≤ δ := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < c * A + 1)).1 hd
    linarith
  calc ‖w‖ = ‖w' + (w - w')‖ := by rw [add_sub_cancel]
    _ ≤ ‖w'‖ + ‖w - w'‖ := norm_add_le _ _
    _ ≤ (c * A + 1) * ‖w - w'‖ := by rw [h3] at h2; nlinarith
    _ ≤ 0 + δ := by linarith

/-! ### The reflection `(s, t) ↦ (-s, t)` -/

/-- `(s, t) ↦ (-s, t)` as a continuous linear map. -/
def reflCLM : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (-ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.id ℝ ℝ)

lemma reflCLM_apply (x : ℝ × ℝ) : reflCLM x = (-x.1, x.2) := rfl

lemma reflCLM_reflCLM (x : ℝ × ℝ) : reflCLM (reflCLM x) = x := by
  simp [reflCLM_apply]

/-- The reflection as a measurable equivalence. -/
def reflEquiv : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ)

lemma reflEquiv_apply (x : ℝ × ℝ) : reflEquiv x = reflCLM x := rfl

lemma measurePreserving_refl : MeasurePreserving reflEquiv cylMeasure cylMeasure := by
  have h : MeasurePreserving reflEquiv (volume : Measure (ℝ × ℝ)) volume :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id volume)
  have hpre : ⇑reflEquiv ⁻¹' ((Set.univ : Set ℝ) ×ˢ Set.Ico (0 : ℝ) 1) =
      (Set.univ : Set ℝ) ×ˢ Set.Ico (0 : ℝ) 1 := by
    ext x
    simp [reflEquiv, MeasurableEquiv.prodCongr]
  have := h.restrict_preimage (s := (Set.univ : Set ℝ) ×ˢ Set.Ico (0 : ℝ) 1)
    (MeasurableSet.univ.prod measurableSet_Ico)
  rw [hpre] at this
  exact this

lemma partialS_comp_refl {φ : ℝ × ℝ → Vec n} (hφ : ContDiff ℝ ∞ φ) (x : ℝ × ℝ) :
    partialS (φ ∘ reflCLM) x = -partialS φ (reflCLM x) := by
  have hd : DifferentiableAt ℝ φ (reflCLM x) := (hφ.differentiable (by simp)).differentiableAt
  unfold partialS
  rw [fderiv_comp x hd reflCLM.differentiableAt, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, reflCLM_apply]
  rw [show ((-(1 : ℝ), (0 : ℝ)) : ℝ × ℝ) = -((1, 0) : ℝ × ℝ) by simp, map_neg]

lemma partialT_comp_refl {φ : ℝ × ℝ → Vec n} (hφ : ContDiff ℝ ∞ φ) (x : ℝ × ℝ) :
    partialT (φ ∘ reflCLM) x = partialT φ (reflCLM x) := by
  have hd : DifferentiableAt ℝ φ (reflCLM x) := (hφ.differentiable (by simp)).differentiableAt
  unfold partialT
  rw [fderiv_comp x hd reflCLM.differentiableAt, ContinuousLinearMap.fderiv]
  simp [reflCLM_apply]

lemma IsTestSection.comp_refl {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) :
    IsTestSection (φ ∘ reflCLM) := by
  obtain ⟨h1, h2, R, hR⟩ := hφ
  refine ⟨h1.comp reflCLM.contDiff, fun s t => ?_, R, fun s t hs => ?_⟩
  · simp only [Function.comp_apply, reflCLM_apply]
    exact h2 (-s) t
  · simp only [Function.comp_apply, reflCLM_apply]
    exact hR (-s) t (by rwa [abs_neg])

/-! ### `D u` of a test section is in `L^p` -/

lemma continuous_crOp (Sinf : ℝ → Mat n) (hc : Continuous Sinf) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) : Continuous (crOp (fun x : ℝ × ℝ => Sinf x.2) u) := by
  have hJ : Continuous fun x => matCLM n (J₀ n) (partialT u x) :=
    (matCLM n (J₀ n)).continuous.comp hu.continuous_partialT
  have hSu : Continuous fun x : ℝ × ℝ => matCLM n (Sinf x.2) (u x) :=
    (continuous_matCLM.comp (hc.comp continuous_snd)).clm_apply hu.continuous
  exact (hu.continuous_partialS.add hJ).add hSu

lemma IsTestSection.memLp_crOp {p : ℝ≥0∞} [Fact (1 ≤ p)] (Sinf : ℝ → Mat n) (hc : Continuous Sinf)
    {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  refine memLp_of_vanish _ (continuous_crOp Sinf hc hu) R fun s t hs => ?_
  simp [crOp, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs, hR s t hs]

lemma crOp_add (S : ℝ × ℝ → Mat n) {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u)
    (hv : IsTestSection v) : crOp S (u + v) = crOp S u + crOp S v := by
  funext x
  simp only [crOp, partialS_add hu hv, partialT_add hu hv, Pi.add_apply, map_add]
  abel

lemma crOp_smul (S : ℝ × ℝ → Mat n) {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    crOp S (c • u) = c • crOp S u := by
  funext x
  simp only [crOp, partialS_smul hu, partialT_smul hu, Pi.smul_apply, map_smul, smul_add]

/-- The images `D u` of test sections, as a subspace of `L^p`. -/
def crImage (p : ℝ≥0∞) [Fact (1 ≤ p)] (Sinf : ℝ → Mat n) : Submodule ℝ (LpCyl n p) where
  carrier := {F | ∃ u, IsTestSection u ∧ (F : ℝ × ℝ → Vec n) =ᵐ[cylMeasure]
    crOp (fun x : ℝ × ℝ => Sinf x.2) u}
  add_mem' := by
    rintro F G ⟨u, hu, hF⟩ ⟨v, hv, hG⟩
    refine ⟨u + v, hu.add hv, ?_⟩
    rw [crOp_add _ hu hv]
    exact (Lp.coeFn_add F G).trans (hF.add hG)
  zero_mem' := by
    refine ⟨0, isTestSection_zero, ?_⟩
    have : crOp (fun x : ℝ × ℝ => Sinf x.2) (0 : ℝ × ℝ → Vec n) = 0 := by
      funext x; simp [crOp, partialS_zero, partialT_zero]
    rw [this]
    exact Lp.coeFn_zero _ _ _
  smul_mem' := by
    rintro c F ⟨u, hu, hF⟩
    refine ⟨c • u, hu.smul c, ?_⟩
    rw [crOp_smul _ hu]
    exact (Lp.coeFn_smul c F).trans (hF.const_smul c)

/-! ### The reduction -/

/-- An `L^q` function annihilating `D(test sections)` vanishes, given the regularity statement
and the a priori bound at the exponent `q`. -/
lemma eq_zero_of_annihilates {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q) (hq' : q ≠ ⊤)
    (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (K1 : ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm q u ≤ c * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) q cylMeasure)
    (g : LpCyl n q)
    (hg : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x) (g x) ∂cylMeasure = 0) : g = 0 := by
  set S : ℝ × ℝ → Mat n := fun x => Sinf x.2 with hSdef
  set η : LpCyl n q := Lp.compMeasurePreserving reflEquiv measurePreserving_refl g with hη
  have hηae : (η : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g ∘ reflEquiv :=
    Lp.coeFn_compMeasurePreserving g measurePreserving_refl
  have hasym : IsAsymptoticTo S Sinf Sinf := by
    refine ⟨hS.1.comp continuous_snd, fun s t => hS.2.1 t, fun ε hε => ⟨0, fun s t i j => ?_⟩⟩
    simp only [hSdef, sub_self, abs_zero]
    exact ⟨fun _ => hε.le, fun _ => hε.le⟩
  have hweak : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (S x)ᵀ (φ x)) (η x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) ((0 : LpCyl n q) x) ∂cylMeasure := by
    intro φ hφ
    have hR : ∫ x, inner ℝ (φ x) ((0 : LpCyl n q) x) ∂cylMeasure = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      filter_upwards [Lp.coeFn_zero (Vec n) q cylMeasure] with x hx
      rw [hx]; simp
    rw [hR]
    have hψ := hφ.comp_refl
    have key : ∀ x, -partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
        Matrix.toEuclideanLin (S x)ᵀ (φ x) = crOp S (φ ∘ reflCLM) (reflEquiv x) := by
      intro x
      rw [reflEquiv_apply, crOp, partialS_comp_refl hφ.1, partialT_comp_refl hφ.1,
        Function.comp_apply, reflCLM_reflCLM]
      simp only [hSdef, (hS.2.2 x.2).eq, reflCLM_apply]
    have e1 : (fun x => inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
        Matrix.toEuclideanLin (S x)ᵀ (φ x)) (η x)) =ᵐ[cylMeasure]
        fun x => (fun y => inner ℝ (crOp S (φ ∘ reflCLM) y) (g y)) (reflEquiv x) := by
      filter_upwards [hηae] with x hx
      rw [key x, hx]
      rfl
    rw [integral_congr_ae e1, measurePreserving_refl.integral_comp'
      (fun y => inner ℝ (crOp S (φ ∘ reflCLM) y) (g y))]
    exact hg _ hψ
  obtain ⟨w, hw, hw1, hw0⟩ := memW1p_of_weak_solution n q hq hq' Sinf Sinf hS hS S hasym η 0 hweak
  have hw0' : crApply S w =ᵐ[cylMeasure] 0 :=
    hw0.trans (Lp.coeFn_zero (Vec n) q cylMeasure)
  have hwz : w = 0 := eq_zero_of_crApply_eq_zero Sinf hS K1 w hw hw0'
  have hη0 : η = 0 := by rw [← hw1, hwz]; rfl
  have : ‖g‖ = 0 := by
    rw [← Lp.norm_compMeasurePreserving g measurePreserving_refl, ← hη, hη0, norm_zero]
  exact norm_eq_zero.1 this

/-- Dense range from the duality statement and the vanishing of annihilators at the conjugate
exponent. -/
theorem denseRange_of_annihilator (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hann : ∀ g : LpCyl n p.conjExponent,
      (∀ u : ℝ × ℝ → Vec n, IsTestSection u →
        ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x) (g x) ∂cylMeasure = 0) → g = 0)
    (f : LpCyl n p) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : ℝ × ℝ → Vec n, IsTestSection u ∧
      eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u - ⇑f) p cylMeasure < ENNReal.ofReal ε := by
  set q := p.conjExponent with hqdef
  have hpq : p.HolderConjugate q := inferInstance
  have hq1 : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).1 (lt_top_iff_ne_top.2 hp')
  have hqt : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  haveI : Fact (1 ≤ q) := ⟨hq1.le⟩
  haveI : SigmaFinite (cylMeasure : Measure (ℝ × ℝ)) := by unfold cylMeasure; infer_instance
  have hdense := dense_of_forall_integral_inner_eq_zero cylMeasure p q hp hp' (crImage p Sinf)
    (fun g hg => hann g fun u hu => by
      have hv := hg ((hu.memLp_crOp (p := p) Sinf hS.1).toLp _)
        ⟨u, hu, (hu.memLp_crOp (p := p) Sinf hS.1).coeFn_toLp⟩
      rw [← hv]
      refine integral_congr_ae ?_
      filter_upwards [(hu.memLp_crOp (p := p) Sinf hS.1).coeFn_toLp] with x hx
      rw [hx])
  obtain ⟨v, hv, hvf⟩ := Metric.mem_closure_iff.1 (hdense f) ε hε
  obtain ⟨u, hu, hvu⟩ := hv
  refine ⟨u, hu, ?_⟩
  have e : crOp (fun x : ℝ × ℝ => Sinf x.2) u - ⇑f =ᵐ[cylMeasure] ⇑(v - f) := by
    filter_upwards [hvu, Lp.coeFn_sub v f] with x h1 h2
    rw [h2, Pi.sub_apply, Pi.sub_apply, h1]
  rw [eLpNorm_congr_ae e, ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (v - f)), ← Lp.norm_def]
  rw [dist_comm, dist_eq_norm] at hvf
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hvf

/-- The `L^p` bound on test sections for `2 ≤ q < ∞`. -/
lemma estimate_of_two_le (n : ℕ) (q : ℝ≥0∞) (hq : 2 ≤ q) (hq' : q ≠ ⊤) (Sinf : ℝ → Mat n)
    (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm q u ≤ c * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) q cylMeasure := by
  obtain ⟨c₁, h₁⟩ := translationInvariant_derivative_estimate n q
    (lt_of_lt_of_le (by norm_num) hq) hq' Sinf hS.1 hS.2.1
  obtain ⟨c₂, h₂⟩ := translationInvariant_Lp_bound n q hq hq' Sinf hS hnd
  refine ⟨c₁ + c₁ * c₂, fun u hu => ?_⟩
  calc w1pNorm q u ≤ c₁ * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) q cylMeasure +
        c₁ * eLpNorm u q cylMeasure := h₁ u hu
    _ ≤ c₁ * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) q cylMeasure +
        c₁ * (c₂ * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) q cylMeasure) := by
        gcongr; exact h₂ u hu
    _ = ((c₁ + c₁ * c₂ : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) q cylMeasure := by
        push_cast; ring

end

end CauchyRiemannIndex

open CauchyRiemannIndex MeasureTheory
open scoped ENNReal NNReal

theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf)
    (f : LpCyl n p) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : ℝ × ℝ → Vec n, IsTestSection u ∧
      eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u - ⇑f) p cylMeasure < ENNReal.ofReal ε := by
  set q := p.conjExponent with hqdef
  refine denseRange_of_annihilator n p hp hp' Sinf hS (fun g hg => ?_) f ε hε
  have hq1 : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).1 (lt_top_iff_ne_top.2 hp')
  have hqt : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  haveI : Fact (1 ≤ q) := ⟨hq1.le⟩
  by_cases hq2 : q < 2
  · exact translationInvariant_annihilator_eq_zero n q hq1 hq2 Sinf hS hnd g hg
  · exact eq_zero_of_annihilates hq1 hqt Sinf hS
      (estimate_of_two_le n q (not_lt.1 hq2) hqt Sinf hS hnd) g hg
