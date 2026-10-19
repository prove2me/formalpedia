-- Prove2me | solution 1 for CauchyRiemannIndex.crIndex_eq_of_asymptoticCZIndex_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T17:28:14.44611+00:00
-- url     : https://prove2.me/submissions/7c51ff36-967e-43a6-8155-0f9bc0338976

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
import Theorems.Thm_CauchyRiemannIndex_crIndex_eq_of_homotopy
import Theorems.Thm_CauchyRiemannIndex_joined_of_asymptoticCZIndex_eq



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
# The index on the cylinder depends only on the end Conley–Zehnder indices

Join the end loops by nondegenerate families `H±` (Thm 3.34) and interpolate:
`F_τ = (1-τ) S + τ T + χ₊ (H₊(τ) - (1-τ) S⁺ - τ T⁺) + χ₋ (H₋(τ) - (1-τ) S⁻ - τ T⁻)`
with continuous cutoffs `χ±`. Every `F_τ` is asymptotic to the nondegenerate loops `H±(τ)`, and
`τ ↦ F_τ` is sup-continuous, so homotopy invariance gives `ind D_S = ind D_T`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma crk_entry {A : Mat n} {M : ℝ} (h : ∀ v : Vec n, ‖Matrix.toEuclideanLin A v‖ ≤ M * ‖v‖)
    (i j : Fin n ⊕ Fin n) : |A i j| ≤ M := by
  have h1 := h (EuclideanSpace.single j 1)
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  refine le_trans ?_ h1
  have e : (Matrix.toEuclideanLin A (EuclideanSpace.single j 1)) i = A i j := by
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_single_one]
  rw [← e, ← Real.norm_eq_abs]
  exact PiLp.norm_apply_le _ i

lemma crk_entry_S {S : ℝ × ℝ → Mat n} {P M : ℝ → Mat n} (hP : IsSymLoop P) (hM : IsSymLoop M)
    (hS : IsAsymptoticTo S P M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x i j, |S x i j| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := crs_Sbound hP hM hS
  exact ⟨C, hC0, fun x i j => crk_entry (hC x) i j⟩

lemma crk_entry_loop {P : ℝ → Mat n} (hP : IsSymLoop P) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t i j, |P t i j| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_loop P hP.1 hP.2.1
  exact ⟨C, hC0, fun t i j => crk_entry (hC t) i j⟩

/-- Uniform continuity in `τ` of a family of loops. -/
lemma crk_unif (H : C(unitInterval × ℝ, Mat n)) (hper : ∀ τ t, H (τ, t + 1) = H (τ, t))
    (τ : unitInterval) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ σ, dist σ τ < δ → ∀ t i j, |H (σ, t) i j - H (τ, t) i j| ≤ ε := by
  have key : ∀ᶠ σ in 𝓝 τ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j, |H (σ, t) i j - H (τ, t) i j| < ε := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have hg : Continuous fun z : unitInterval × ℝ => |H z i j - H (τ, z.2) i j| := by
      have h1 : Continuous fun z : unitInterval × ℝ => H z i j :=
        (continuous_apply j).comp ((continuous_apply i).comp H.continuous)
      have h2 : Continuous fun z : unitInterval × ℝ => H (τ, z.2) i j :=
        (continuous_apply j).comp ((continuous_apply i).comp
          (H.continuous.comp (continuous_const.prodMk continuous_snd)))
      exact (h1.sub h2).abs
    have h0 : (fun z : unitInterval × ℝ => |H z i j - H (τ, z.2) i j|) (τ, t) < ε := by
      simpa using hε
    exact hg.continuousAt.eventually_lt continuousAt_const h0
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 key
  refine ⟨δ, hδ, fun σ hσ t i j => ?_⟩
  have hp : ∀ ρ : unitInterval, H (ρ, Int.fract t) = H (ρ, t) := fun ρ => by
    have hP : Function.Periodic (fun t => H (ρ, t)) 1 := fun t => hper ρ t
    have := hP.sub_int_mul_eq (x := t) ⌊t⌋
    rw [mul_one] at this
    exact this
  rw [← hp σ, ← hp τ]
  exact (hball hσ (Int.fract t) ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩ i j).le

/-- The cutoff `s ↦ clamp(s, 0, 1)`. -/
def crkχ (s : ℝ) : ℝ := max 0 (min s 1)

lemma crkχ_cont : Continuous crkχ := by unfold crkχ; fun_prop
lemma crkχ_nonneg (s : ℝ) : 0 ≤ crkχ s := le_max_left _ _
lemma crkχ_le (s : ℝ) : crkχ s ≤ 1 := max_le zero_le_one (min_le_right _ _)
lemma crkχ_of_le {s : ℝ} (h : s ≤ 0) : crkχ s = 0 := by
  unfold crkχ; rw [max_eq_left]; exact (min_le_left _ _).trans h
lemma crkχ_of_ge {s : ℝ} (h : 1 ≤ s) : crkχ s = 1 := by
  unfold crkχ; rw [min_eq_right h, max_eq_right zero_le_one]

theorem crIndex_eq_of_asymptoticCZIndex_eq_aux (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤) (Splus Sminus Tplus Tminus : ℝ → Mat n)
    (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (hTplus : IsSymLoop Tplus) (hTminus : IsSymLoop Tminus)
    (hnSplus : IsNondegenerate Splus) (hnSminus : IsNondegenerate Sminus)
    (hnTplus : IsNondegenerate Tplus) (hnTminus : IsNondegenerate Tminus)
    (hμplus : asymptoticCZIndex Splus = asymptoticCZIndex Tplus)
    (hμminus : asymptoticCZIndex Sminus = asymptoticCZIndex Tminus)
    (S T : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus)
    (hT : IsAsymptoticTo T Tplus Tminus) :
    crIndex p S = crIndex p T := by
  obtain ⟨Hp, hHp0, hHp1, hHp⟩ :=
    joined_of_asymptoticCZIndex_eq n Splus Tplus hSplus hTplus hnSplus hnTplus hμplus
  obtain ⟨Hm, hHm0, hHm1, hHm⟩ :=
    joined_of_asymptoticCZIndex_eq n Sminus Tminus hSminus hTminus hnSminus hnTminus hμminus
  set F : unitInterval → ℝ × ℝ → Mat n := fun τ x =>
    (1 - (τ : ℝ)) • S x + (τ : ℝ) • T x +
      crkχ x.1 • (Hp (τ, x.2) - (1 - (τ : ℝ)) • Splus x.2 - (τ : ℝ) • Tplus x.2) +
      crkχ (-x.1) • (Hm (τ, x.2) - (1 - (τ : ℝ)) • Sminus x.2 - (τ : ℝ) • Tminus x.2) with hFdef
  have hF : ∀ τ x i j, F τ x i j =
      (1 - (τ : ℝ)) * S x i j + τ * T x i j +
        crkχ x.1 * (Hp (τ, x.2) i j - (1 - (τ : ℝ)) * Splus x.2 i j - τ * Tplus x.2 i j) +
        crkχ (-x.1) * (Hm (τ, x.2) i j - (1 - (τ : ℝ)) * Sminus x.2 i j - τ * Tminus x.2 i j) := by
    intro τ x i j
    simp [hFdef, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  have hper : ∀ (H : C(unitInterval × ℝ, Mat n)),
      (∀ τ, IsSymLoop (fun t => H (τ, t))) → ∀ τ t, H (τ, t + 1) = H (τ, t) :=
    fun H h τ t => (h τ).2.1 t
  have hpp := hper Hp fun τ => (hHp τ).1
  have hmp := hper Hm fun τ => (hHm τ).1
  -- asymptotics of each `F τ`
  have hasym : ∀ τ, IsAsymptoticTo (F τ) (fun t => Hp (τ, t)) (fun t => Hm (τ, t)) := by
    intro τ
    refine ⟨?_, ?_, ?_⟩
    · have cS := hS.1
      have cT := hT.1
      have c1 := hSplus.1
      have c2 := hTplus.1
      have c3 := hSminus.1
      have c4 := hTminus.1
      have cχ := crkχ_cont
      have cHp := Hp.continuous
      have cHm := Hm.continuous
      simp only [hFdef]
      fun_prop
    · intro s t
      simp only [hFdef]
      rw [hS.2.1, hT.2.1, hpp, hmp, hSplus.2.1 t, hTplus.2.1 t, hSminus.2.1 t, hTminus.2.1 t]
    · intro ε hε
      obtain ⟨R1, hR1⟩ := hS.2.2 ε hε
      obtain ⟨R2, hR2⟩ := hT.2.2 ε hε
      refine ⟨max (max R1 R2) 1, fun s t i j => ⟨fun hs => ?_, fun hs => ?_⟩⟩
      · have h1 : R1 ≤ s := (le_max_left _ _).trans ((le_max_left _ _).trans hs)
        have h2 : R2 ≤ s := (le_max_right _ _).trans ((le_max_left _ _).trans hs)
        have h3 : 1 ≤ s := (le_max_right _ _).trans hs
        rw [hF, crkχ_of_ge h3, crkχ_of_le (by linarith)]
        have e1 := (hR1 s t i j).1 h1
        have e2 := (hR2 s t i j).1 h2
        have hτ0 : 0 ≤ (τ : ℝ) := τ.2.1
        have hτ1 : (τ : ℝ) ≤ 1 := τ.2.2
        have : (1 - (τ : ℝ)) * S (s, t) i j + τ * T (s, t) i j +
            1 * (Hp (τ, t) i j - (1 - (τ : ℝ)) * Splus t i j - τ * Tplus t i j) +
            0 * (Hm (τ, t) i j - (1 - (τ : ℝ)) * Sminus t i j - τ * Tminus t i j) - Hp (τ, t) i j =
            (1 - (τ : ℝ)) * (S (s, t) i j - Splus t i j) + τ * (T (s, t) i j - Tplus t i j) := by ring
        rw [this]
        calc |(1 - (τ : ℝ)) * (S (s, t) i j - Splus t i j) + τ * (T (s, t) i j - Tplus t i j)|
            ≤ (1 - (τ : ℝ)) * |S (s, t) i j - Splus t i j| + τ * |T (s, t) i j - Tplus t i j| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hτ0]
          _ ≤ (1 - (τ : ℝ)) * ε + τ * ε := by gcongr
          _ = ε := by ring
      · have h1 : s ≤ -R1 := by
          have := (le_max_left R1 R2).trans (le_max_left (max R1 R2) 1); linarith
        have h2 : s ≤ -R2 := by
          have := (le_max_right R1 R2).trans (le_max_left (max R1 R2) 1); linarith
        have h3 : 1 ≤ -s := by have := le_max_right (max R1 R2) 1; linarith
        rw [hF, crkχ_of_ge h3, crkχ_of_le (by linarith)]
        have e1 := (hR1 s t i j).2 h1
        have e2 := (hR2 s t i j).2 h2
        have hτ0 : 0 ≤ (τ : ℝ) := τ.2.1
        have hτ1 : (τ : ℝ) ≤ 1 := τ.2.2
        have : (1 - (τ : ℝ)) * S (s, t) i j + τ * T (s, t) i j +
            0 * (Hp (τ, t) i j - (1 - (τ : ℝ)) * Splus t i j - τ * Tplus t i j) +
            1 * (Hm (τ, t) i j - (1 - (τ : ℝ)) * Sminus t i j - τ * Tminus t i j) - Hm (τ, t) i j =
            (1 - (τ : ℝ)) * (S (s, t) i j - Sminus t i j) + τ * (T (s, t) i j - Tminus t i j) := by
          ring
        rw [this]
        calc |(1 - (τ : ℝ)) * (S (s, t) i j - Sminus t i j) + τ * (T (s, t) i j - Tminus t i j)|
            ≤ (1 - (τ : ℝ)) * |S (s, t) i j - Sminus t i j| + τ * |T (s, t) i j - Tminus t i j| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hτ0]
          _ ≤ (1 - (τ : ℝ)) * ε + τ * ε := by gcongr
          _ = ε := by ring
  -- sup-continuity in `τ`
  have hcont : ∀ τ, ∀ ε > 0, ∃ δ > 0, ∀ σ, dist σ τ < δ → ∀ x i j,
      |F σ x i j - F τ x i j| ≤ ε := by
    intro τ ε hε
    obtain ⟨C1, hC1, hb1⟩ := crk_entry_S hSplus hSminus hS
    obtain ⟨C2, hC2, hb2⟩ := crk_entry_S hTplus hTminus hT
    obtain ⟨C3, hC3, hb3⟩ := crk_entry_loop hSplus
    obtain ⟨C4, hC4, hb4⟩ := crk_entry_loop hTplus
    obtain ⟨C5, hC5, hb5⟩ := crk_entry_loop hSminus
    obtain ⟨C6, hC6, hb6⟩ := crk_entry_loop hTminus
    set K := C1 + C2 + C3 + C4 + C5 + C6 with hK
    have hK0 : 0 ≤ K := by positivity
    obtain ⟨δp, hδp, hup⟩ := crk_unif Hp hpp τ (ε := ε / 3) (by positivity)
    obtain ⟨δm, hδm, hum⟩ := crk_unif Hm hmp τ (ε := ε / 3) (by positivity)
    refine ⟨min (min δp δm) (ε / (3 * (K + 1))), by positivity, fun σ hσ x i j => ?_⟩
    have hσp : dist σ τ < δp := hσ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hσm : dist σ τ < δm := hσ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hσd : |(σ : ℝ) - τ| < ε / (3 * (K + 1)) := by
      have := hσ.trans_le (min_le_right _ _)
      rwa [Subtype.dist_eq, Real.dist_eq] at this
    set d : ℝ := (σ : ℝ) - τ with hd
    have e : F σ x i j - F τ x i j =
        d * (T x i j - S x i j) +
          crkχ x.1 * ((Hp (σ, x.2) i j - Hp (τ, x.2) i j) - d * (Tplus x.2 i j - Splus x.2 i j)) +
          crkχ (-x.1) * ((Hm (σ, x.2) i j - Hm (τ, x.2) i j) -
            d * (Tminus x.2 i j - Sminus x.2 i j)) := by
      rw [hF, hF, hd]; ring
    rw [e]
    have a1 : |d * (T x i j - S x i j)| ≤ |d| * (C1 + C2) := by
      rw [abs_mul]; gcongr
      exact (abs_sub _ _).trans (by linarith [hb1 x i j, hb2 x i j])
    have a2 : |crkχ x.1 * ((Hp (σ, x.2) i j - Hp (τ, x.2) i j) -
        d * (Tplus x.2 i j - Splus x.2 i j))| ≤ ε / 3 + |d| * (C3 + C4) := by
      rw [abs_mul, abs_of_nonneg (crkχ_nonneg _)]
      have : |(Hp (σ, x.2) i j - Hp (τ, x.2) i j) - d * (Tplus x.2 i j - Splus x.2 i j)| ≤
          ε / 3 + |d| * (C3 + C4) := by
        refine (abs_sub _ _).trans (add_le_add (hup σ hσp x.2 i j) ?_)
        rw [abs_mul]; gcongr
        exact (abs_sub _ _).trans (by linarith [hb3 x.2 i j, hb4 x.2 i j])
      calc crkχ x.1 * _ ≤ 1 * (ε / 3 + |d| * (C3 + C4)) :=
            mul_le_mul (crkχ_le _) this (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have a3 : |crkχ (-x.1) * ((Hm (σ, x.2) i j - Hm (τ, x.2) i j) -
        d * (Tminus x.2 i j - Sminus x.2 i j))| ≤ ε / 3 + |d| * (C5 + C6) := by
      rw [abs_mul, abs_of_nonneg (crkχ_nonneg _)]
      have : |(Hm (σ, x.2) i j - Hm (τ, x.2) i j) - d * (Tminus x.2 i j - Sminus x.2 i j)| ≤
          ε / 3 + |d| * (C5 + C6) := by
        refine (abs_sub _ _).trans (add_le_add (hum σ hσm x.2 i j) ?_)
        rw [abs_mul]; gcongr
        exact (abs_sub _ _).trans (by linarith [hb5 x.2 i j, hb6 x.2 i j])
      calc crkχ (-x.1) * _ ≤ 1 * (ε / 3 + |d| * (C5 + C6)) :=
            mul_le_mul (crkχ_le _) this (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hdK : |d| * K ≤ ε / 3 := by
      have h3 : 0 < 3 * (K + 1) := by positivity
      have : |d| * (3 * (K + 1)) < ε := by
        have := (lt_div_iff₀ h3).1 hσd; linarith
      nlinarith [abs_nonneg d]
    calc _ ≤ |d * (T x i j - S x i j)| +
          |crkχ x.1 * ((Hp (σ, x.2) i j - Hp (τ, x.2) i j) - d * (Tplus x.2 i j - Splus x.2 i j))| +
          |crkχ (-x.1) * ((Hm (σ, x.2) i j - Hm (τ, x.2) i j) -
            d * (Tminus x.2 i j - Sminus x.2 i j))| := abs_add_three _ _ _
      _ ≤ |d| * (C1 + C2) + (ε / 3 + |d| * (C3 + C4)) + (ε / 3 + |d| * (C5 + C6)) := by
          gcongr
      _ = 2 * (ε / 3) + |d| * K := by rw [hK]; ring
      _ ≤ ε := by linarith
  have hmain := crIndex_eq_of_homotopy n p hp hp' F (fun τ t => Hp (τ, t)) (fun τ t => Hm (τ, t))
    (fun τ => (hHp τ).1) (fun τ => (hHm τ).1) (fun τ => (hHp τ).2) (fun τ => (hHm τ).2)
    hasym hcont
  have h0 : F 0 = S := by
    funext x; ext i j
    rw [hF, hHp0, hHm0]
    simp
  have h1 : F 1 = T := by
    funext x; ext i j
    rw [hF, hHp1, hHm1]
    simp
  rw [← h0, ← h1]
  exact hmain

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤) (Splus Sminus Tplus Tminus : ℝ → Mat n)
    (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (hTplus : IsSymLoop Tplus) (hTminus : IsSymLoop Tminus)
    (hnSplus : IsNondegenerate Splus) (hnSminus : IsNondegenerate Sminus)
    (hnTplus : IsNondegenerate Tplus) (hnTminus : IsNondegenerate Tminus)
    (hμplus : asymptoticCZIndex Splus = asymptoticCZIndex Tplus)
    (hμminus : asymptoticCZIndex Sminus = asymptoticCZIndex Tminus)
    (S T : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus)
    (hT : IsAsymptoticTo T Tplus Tminus) :
    crIndex p S = crIndex p T :=
  crIndex_eq_of_asymptoticCZIndex_eq_aux n p hp hp' Splus Sminus Tplus Tminus hSplus hSminus hTplus hTminus hnSplus hnSminus hnTplus hnTminus hμplus hμminus S T hS hT
