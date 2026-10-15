-- Prove2me | solution 1 for CauchyRiemannIndex.translationInvariant_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-13T22:12:20.190994+00:00
-- url     : https://prove2.me/submissions/f8855ebc-7c2f-4efa-b87a-9c43af0c7f00

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_estimate
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_denseRange

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

/-- The closure argument: an a priori bound on test sections and dense range on test sections
give `ker = 0` and `range = L^p`. -/
theorem bijective_of_estimate_of_dense (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (K1 : ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure)
    (K2 : ∀ (f : LpCyl n p) (ε : ℝ), 0 < ε → ∃ u : ℝ × ℝ → Vec n, IsTestSection u ∧
      eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u - ⇑f) p cylMeasure < ENNReal.ofReal ε) :
    crKernel p (fun x : ℝ × ℝ => Sinf x.2) = ⊥ ∧ crRange p (fun x : ℝ × ℝ => Sinf x.2) = ⊤ := by
  set S : ℝ × ℝ → Mat n := fun x => Sinf x.2 with hSdef
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  obtain ⟨M, hM0, hM⟩ := exists_bound_loop Sinf hS.1 hS.2.1
  obtain ⟨MJ, hMJ0, hMJ⟩ := exists_bound_mat (J₀ n)
  obtain ⟨c, hc⟩ := K1
  set A : ℝ := 1 + MJ + M with hA
  have hA0 : 0 ≤ A := by positivity
  -- Lipschitz bound for `crApply`
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
  -- the bound on test triples
  have hT : ∀ w ∈ testTriples n p, ENNReal.ofReal ‖w‖ ≤ c * eLpNorm (crApply S w) p cylMeasure := by
    rintro w ⟨u, hu, h1, h2, h3⟩
    rw [eLpNorm_congr_ae (crApply_ae_crOp S h1 h2 h3)]
    exact (ofReal_norm_le_w1pNorm h1 h2 h3).trans (hc u hu)
  have hcoe : (c : ℝ≥0∞) = ENNReal.ofReal c := (ENNReal.ofReal_coe_nnreal).symm
  have hW : ∀ w ∈ W1p p n, w ∈ closure (testTriples n p) := by
    intro w hw
    have : w ∈ ((Submodule.span ℝ (testTriples n p)).topologicalClosure : Set (Triple n p)) := hw
    rw [Submodule.topologicalClosure_coe] at this
    exact closure_mono span_testTriples_subset this
  constructor
  · -- kernel
    have hker : ∀ w ∈ W1p p n, crApply S w =ᵐ[cylMeasure] 0 → w = 0 := by
      intro w hw h0
      refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
      obtain ⟨w', hw', hd⟩ := Metric.mem_closure_iff.1 (hW w hw) (δ / (c * A + 1)) (by positivity)
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
    refine eq_bot_iff.2 (Submodule.span_le.2 fun w hw => ?_)
    exact (Submodule.mem_bot ℝ).2 (hker w hw.1 hw.2)
  · -- range
    refine eq_top_iff.2 fun f _ => Submodule.subset_span ?_
    choose u hu hlt using fun k : ℕ => K2 f (1 / ((k : ℝ) + 1)) (by positivity)
    set w : ℕ → Triple n p := fun k => testTriple (hu k) with hwdef
    have hwT : ∀ k, w k ∈ testTriples n p := fun k => testTriple_mem (hu k)
    have hwf : ∀ k, eLpNorm (crApply S (w k) - ⇑f) p cylMeasure < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
      intro k
      have : crApply S (w k) - ⇑f =ᵐ[cylMeasure] crOp S (u k) - ⇑f :=
        (crApply_ae_crOp S ((hu k).memLp (p := p)).coeFn_toLp ((hu k).memLp_partialS (p := p)).coeFn_toLp
          ((hu k).memLp_partialT (p := p)).coeFn_toLp).sub
          EventuallyEq.rfl
      rw [eLpNorm_congr_ae this]
      exact hlt k
    have hmeas : ∀ k, AEStronglyMeasurable (crApply S (w k) - ⇑f) cylMeasure := fun k =>
      (aestronglyMeasurable_crApply Sinf hS.1 _).sub (Lp.aestronglyMeasurable f)
    -- Cauchy
    have hdist : ∀ k m, ‖w k - w m‖ ≤ c * (1 / ((k : ℝ) + 1) + 1 / ((m : ℝ) + 1)) := by
      intro k m
      have hmem : w k - w m ∈ testTriples n p :=
        span_testTriples_subset (Submodule.sub_mem _ (Submodule.subset_span (hwT k))
          (Submodule.subset_span (hwT m)))
      have e : crApply S (w k - w m) =ᵐ[cylMeasure]
          (crApply S (w k) - ⇑f) - (crApply S (w m) - ⇑f) := by
        filter_upwards [crApply_sub_ae S (w k) (w m)] with x hx
        rw [hx]; simp
      refine (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 ?_
      calc ENNReal.ofReal ‖w k - w m‖ ≤ c * eLpNorm (crApply S (w k - w m)) p cylMeasure := hT _ hmem
        _ = c * eLpNorm ((crApply S (w k) - ⇑f) - (crApply S (w m) - ⇑f)) p cylMeasure := by
          rw [eLpNorm_congr_ae e]
        _ ≤ c * (eLpNorm (crApply S (w k) - ⇑f) p cylMeasure +
              eLpNorm (crApply S (w m) - ⇑f) p cylMeasure) := by
          gcongr; exact eLpNorm_sub_le (hmeas k) (hmeas m) hp1
        _ ≤ c * (ENNReal.ofReal (1 / ((k : ℝ) + 1)) + ENNReal.ofReal (1 / ((m : ℝ) + 1))) := by
          gcongr
          · exact (hwf k).le
          · exact (hwf m).le
        _ = ENNReal.ofReal (c * (1 / ((k : ℝ) + 1) + 1 / ((m : ℝ) + 1))) := by
          rw [hcoe, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity)]
    have hcauchy : CauchySeq w := by
      refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
      obtain ⟨N, hN⟩ := exists_nat_gt (2 * (c + 1) / ε)
      refine ⟨N, fun k hk => ?_⟩
      rw [dist_eq_norm]
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le hN1 (by exact_mod_cast Nat.add_le_add_right hk 1)
      have hc0 : (0 : ℝ) ≤ c := c.2
      have hb : c * (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1)) < ε := by
        rw [div_lt_iff₀ hε] at hN
        have : 2 * (c + 1) < ε * ((N : ℝ) + 1) := by nlinarith
        rw [← two_mul, ← mul_assoc, mul_one_div, div_lt_iff₀ hN1]
        nlinarith
      calc ‖w k - w N‖ ≤ c * (1 / ((k : ℝ) + 1) + 1 / ((N : ℝ) + 1)) := hdist k N
        _ ≤ c * (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1)) := by gcongr
        _ < ε := hb
    haveI : CompleteSpace (LpCyl n p) := inferInstance
    haveI : CompleteSpace (Triple n p) := inferInstance
    obtain ⟨wl, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hW1 : wl ∈ W1p p n := by
      refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
        (Eventually.of_forall fun k => ?_)
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (hwT k))
    refine ⟨wl, hW1, ?_⟩
    -- `crApply S wl = f` a.e.
    have hbound : ∀ k, eLpNorm (crApply S wl - ⇑f) p cylMeasure ≤
        ENNReal.ofReal A * ENNReal.ofReal ‖wl - w k‖ + ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
      intro k
      have e : crApply S wl - ⇑f = (crApply S wl - crApply S (w k)) + (crApply S (w k) - ⇑f) := by
        abel
      rw [e]
      refine (eLpNorm_add_le ((aestronglyMeasurable_crApply Sinf hS.1 _).sub
        (aestronglyMeasurable_crApply Sinf hS.1 _)) (hmeas k) hp1).trans ?_
      gcongr
      · exact hLip _ _
      · exact (hwf k).le
    have htend : Tendsto (fun k : ℕ => ENNReal.ofReal A * ENNReal.ofReal ‖wl - w k‖ +
        ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      have t1 : Tendsto (fun k : ℕ => ENNReal.ofReal ‖wl - w k‖) atTop (𝓝 0) := by
        have : Tendsto (fun k : ℕ => ‖wl - w k‖) atTop (𝓝 0) := by
          have := (tendsto_iff_norm_sub_tendsto_zero.1 hlim)
          simpa [norm_sub_rev] using this
        simpa using ENNReal.tendsto_ofReal this
      have t2 : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      have t3 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal A) t1 (Or.inr ENNReal.ofReal_ne_top)
      simpa using t3.add t2
    have h0 : eLpNorm (crApply S wl - ⇑f) p cylMeasure = 0 :=
      le_antisymm (ge_of_tendsto' htend hbound) bot_le
    have hae := (eLpNorm_eq_zero_iff ((aestronglyMeasurable_crApply Sinf hS.1 _).sub
      (Lp.aestronglyMeasurable f)) hp0).1 h0
    filter_upwards [hae] with x hx
    exact (sub_eq_zero.1 hx).symm

end

end CauchyRiemannIndex

open CauchyRiemannIndex MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    crKernel p (fun x : ℝ × ℝ => Sinf x.2) = ⊥ ∧ crRange p (fun x : ℝ × ℝ => Sinf x.2) = ⊤ :=
  bijective_of_estimate_of_dense Sinf hS (translationInvariant_estimate n p hp hp' Sinf hS hnd)
    (fun f ε hε => translationInvariant_denseRange n p hp hp' Sinf hS hnd f ε hε)
