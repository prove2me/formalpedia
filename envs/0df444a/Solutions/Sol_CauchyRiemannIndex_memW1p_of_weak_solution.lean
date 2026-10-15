-- Prove2me | solution 1 for CauchyRiemannIndex.memW1p_of_weak_solution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T09:55:49.089964+00:00
-- url     : https://prove2.me/submissions/f52622ac-1999-4776-9698-e1ff3cfb2639

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
import Theorems.Thm_CauchyRiemannIndex_weak_solution_graph_approx
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_derivative_estimate
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

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

-- ===== Scratch/CR46Parent.lean =====
/-!
# Wendl, Proposition 4.6 (`k = 1`): weak `L^p` solutions of `D_S η = f` lie in `W^{1,p}`

`S` is bounded, so `D₀ η = f - S η` weakly with `f - S η ∈ L^p`. Test sections `u_k` with
`u_k → η`, `D₀ u_k → f - S η` in `L^p` (child `weak_solution_graph_approx`) have Cauchy triples
`(u_k, ∂ₛu_k, ∂ₜu_k)` by the estimate of `translationInvariant_derivative_estimate` at `S∞ = 0`;
their limit `w ∈ W^{1,p}` has `w₁ = η` and `D_S w = f`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma c46p_per {β : Type*} {F : ℝ × ℝ → β} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (s t : ℝ) :
    F (s, Int.fract t) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hF s t
  have := hp.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at this
  exact this

lemma c46p_matbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ D : Mat n, (∀ i j, |D i j| ≤ 1) → ‖matCLM n D‖ ≤ B := by
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
lemma c46p_Sbound {S : ℝ × ℝ → Mat n} {Splus Sminus : ℝ → Mat n} (hSp : IsSymLoop Splus)
    (hSm : IsSymLoop Sminus) (hS : IsAsymptoticTo S Splus Sminus) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖ := by
  obtain ⟨Mp, hMp0, hMp⟩ := exists_bound_loop Splus hSp.1 hSp.2.1
  obtain ⟨Mm, hMm0, hMm⟩ := exists_bound_loop Sminus hSm.1 hSm.2.1
  obtain ⟨B, hB0, hB⟩ := c46p_matbound (n := n)
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
  have e : S (x.1, Int.fract x.2) = S x := c46p_per hS.2.1 x.1 x.2
  simp only [Function.comp, e] at hCx
  rw [← matCLM_apply]
  calc ‖matCLM n (S x) v‖ ≤ ‖matCLM n (S x)‖ * ‖v‖ := (matCLM n _).le_opNorm v
    _ ≤ max C 0 * ‖v‖ := by gcongr; exact hCx.trans (le_max_left _ _)
    _ ≤ (max C 0 + B + Mp + Mm) * ‖v‖ := by nlinarith

lemma c46p_bound_per {E : Type*} [NormedAddCommGroup E] {Φ : ℝ × ℝ → E} (hΦ : Continuous Φ)
    (hΦper : ∀ s t, Φ (s, t + 1) = Φ (s, t)) {R : ℝ} (hΦR : ∀ s t, R < |s| → Φ (s, t) = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖Φ x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : R < |x.1|
  · have : Φ x = 0 := hΦR x.1 x.2 hx
    rw [this, norm_zero]
    exact le_max_right _ _
  · push_neg at hx
    rw [← c46p_per hΦper x.1 x.2]
    exact (hM _ (Set.mk_mem_prod (Set.mem_Icc.2 (abs_le.1 hx))
      (Set.mem_Icc.2 ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩))).trans (le_max_left _ _)

lemma c46p_integrable_inner {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : ℝ × ℝ → Vec n} (hΦ : Continuous Φ)
    (hper : ∀ s t, Φ (s, t + 1) = Φ (s, t)) {R : ℝ} (hR : ∀ s t, R < |s| → Φ (s, t) = 0)
    {h : ℝ × ℝ → Vec n} (hh : AEStronglyMeasurable h cylMeasure) (hm : MemLp h p cylMeasure) :
    Integrable (fun x => inner ℝ (Φ x) (h x)) cylMeasure := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨M, hM0, hM⟩ := c46p_bound_per hΦ hper hR
  set K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.univ with hK
  have hKm : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hKf : cylMeasure K ≠ ⊤ := by
    rw [cylMeasure_eq_prod, hK, Measure.prod_prod]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  haveI : IsFiniteMeasure (cylMeasure.restrict K) := isFiniteMeasure_restrict.2 hKf
  have hhK : IntegrableOn h K cylMeasure := (hm.restrict K).integrable hp1
  have hb : Integrable (K.indicator fun x => M * ‖h x‖) cylMeasure :=
    (show IntegrableOn (fun x => M * ‖h x‖) K cylMeasure from hhK.norm.const_mul M).integrable_indicator hKm
  refine hb.mono' (hΦ.aestronglyMeasurable.inner hh) (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  · rw [Set.indicator_of_notMem hx]
    have hs : R < |x.1| := by
      by_contra hc
      push_neg at hc
      exact hx ⟨abs_le.1 hc, Set.mem_univ _⟩
    have : Φ x = 0 := hR x.1 x.2 hs
    simp [this]

lemma c46p_shift_eq {ψ : ℝ × ℝ → Vec n} (hper : ∀ s t, ψ (s, t + 1) = ψ (s, t)) :
    (fun x : ℝ × ℝ => ψ (x + (0, 1))) = ψ := by
  funext x
  show ψ (x.1 + 0, x.2 + 1) = ψ x
  rw [add_zero, hper]

lemma c46p_partialS_per {ψ : ℝ × ℝ → Vec n} (hper : ∀ s t, ψ (s, t + 1) = ψ (s, t)) (s t : ℝ) :
    partialS ψ (s, t + 1) = partialS ψ (s, t) := by
  have h : partialS (fun x : ℝ × ℝ => ψ (x + (0, 1))) (s, t) = partialS ψ ((s, t) + (0, 1)) := by
    simp only [partialS]; rw [fderiv_comp_add_right]
  rw [c46p_shift_eq hper] at h
  rw [h]; simp

lemma c46p_partialT_per {ψ : ℝ × ℝ → Vec n} (hper : ∀ s t, ψ (s, t + 1) = ψ (s, t)) (s t : ℝ) :
    partialT ψ (s, t + 1) = partialT ψ (s, t) := by
  have h : partialT (fun x : ℝ × ℝ => ψ (x + (0, 1))) (s, t) = partialT ψ ((s, t) + (0, 1)) := by
    simp only [partialT]; rw [fderiv_comp_add_right]
  rw [c46p_shift_eq hper] at h
  rw [h]; simp

lemma c46p_crOp_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    crOp (fun _ : ℝ × ℝ => (0 : Mat n)) (u - v) =
      crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u - crOp (fun _ : ℝ × ℝ => (0 : Mat n)) v := by
  funext x
  simp only [crOp, partialS_sub hu hv, partialT_sub hu hv, Pi.sub_apply, map_sub]
  abel

lemma c46p_eLpNorm_sub_le {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b c : ℝ × ℝ → Vec n}
    (ha : AEStronglyMeasurable a cylMeasure) (hb : AEStronglyMeasurable b cylMeasure)
    (hc : AEStronglyMeasurable c cylMeasure) :
    eLpNorm (a - c) p cylMeasure ≤ eLpNorm (a - b) p cylMeasure + eLpNorm (c - b) p cylMeasure := by
  have hp1 : 1 ≤ p := Fact.out
  calc eLpNorm (a - c) p cylMeasure = eLpNorm ((a - b) + (b - c)) p cylMeasure := by
        rw [sub_add_sub_cancel]
    _ ≤ eLpNorm (a - b) p cylMeasure + eLpNorm (b - c) p cylMeasure :=
        eLpNorm_add_le (ha.sub hb) (hb.sub hc) hp1
    _ = eLpNorm (a - b) p cylMeasure + eLpNorm (c - b) p cylMeasure := by
        rw [eLpNorm_sub_comm b c]

lemma c46p_cont_crOp0 {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u) :=
  (hu.continuous_partialS.add ((matCLM n (J₀ n)).continuous.comp hu.continuous_partialT)).add
    ((matCLM n 0).continuous.comp hu.continuous)

theorem memW1p_aux (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (η f : LpCyl n p)
    (hweak : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (S x)ᵀ (φ x)) (η x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) (f x) ∂cylMeasure) :
    ∃ w ∈ W1p p n, w.1 = η ∧ crApply S w =ᵐ[cylMeasure] (f : ℝ × ℝ → Vec n) := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨M, hM0, hM⟩ := c46p_Sbound hSplus hSminus hS
  -- `S η ∈ L^p` and `g = f - S η`
  set Sη : ℝ × ℝ → Vec n := fun x => Matrix.toEuclideanLin (S x) (η x) with hSη
  have hSηm : AEStronglyMeasurable Sη cylMeasure :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (A : Vec n →L[ℝ] Vec n) (v : Vec n) => A v)
      (continuous_fst.clm_apply continuous_snd)
      ((continuous_matCLM.comp hS.1).aestronglyMeasurable) (Lp.aestronglyMeasurable η)
  have hSηL : MemLp Sη p cylMeasure :=
    ((Lp.memLp η).const_smul M).of_le hSηm (ae_of_all _ fun x => by
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hM0]; exact hM x (η x))
  set g0 : ℝ × ℝ → Vec n := fun x => f x - Sη x with hg0
  have hg0L : MemLp g0 p cylMeasure := (Lp.memLp f).sub hSηL
  set G : LpCyl n p := hg0L.toLp g0 with hG
  have hGae : (G : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g0 := hg0L.coeFn_toLp
  -- the weak equation for `(η, G)`
  have hw0 : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x)) (η x)
          ∂cylMeasure = ∫ x, inner ℝ (φ x) (G x) ∂cylMeasure := by
    intro φ hφ
    obtain ⟨R, hR⟩ := hφ.2.2
    set A : ℝ × ℝ → Vec n := fun x => -partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x)
      with hA
    set B : ℝ × ℝ → Vec n := fun x => Matrix.toEuclideanLin (S x)ᵀ (φ x) with hB
    have hAc : Continuous A :=
      hφ.continuous_partialS.neg.add ((matCLM n (J₀ n)).continuous.comp hφ.continuous_partialT)
    have hAp : ∀ s t, A (s, t + 1) = A (s, t) := fun s t => by
      simp only [hA, c46p_partialS_per hφ.2.1, c46p_partialT_per hφ.2.1]
    have hAv : ∀ s t, R < |s| → A (s, t) = 0 := fun s t hs => by
      simp only [hA, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs, neg_zero, map_zero,
        add_zero]
    have hBc : Continuous B :=
      (continuous_matCLM.comp hS.1.matrix_transpose).clm_apply hφ.continuous
    have hBp : ∀ s t, B (s, t + 1) = B (s, t) := fun s t => by
      simp only [hB, hS.2.1, hφ.2.1]
    have hBv : ∀ s t, R < |s| → B (s, t) = 0 := fun s t hs => by
      simp only [hB, hR s t hs, map_zero]
    have i1 := c46p_integrable_inner hAc hAp hAv (Lp.aestronglyMeasurable η) (Lp.memLp η)
    have i2 := c46p_integrable_inner hBc hBp hBv (Lp.aestronglyMeasurable η) (Lp.memLp η)
    have i3 := c46p_integrable_inner hφ.continuous hφ.2.1 hR (Lp.aestronglyMeasurable f)
      (Lp.memLp f)
    have i4 := c46p_integrable_inner hφ.continuous hφ.2.1 hR hSηm hSηL
    have h := hweak φ hφ
    have e1 : ∀ x, inner ℝ (A x + B x) (η x) = inner ℝ (A x) (η x) + inner ℝ (φ x) (Sη x) := by
      intro x
      rw [inner_add_left, hB, hSη]
      simp only
      rw [inner_toEuclideanLin, Matrix.transpose_transpose]
    have h' : ∫ x, inner ℝ (A x + B x) (η x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) (f x) ∂cylMeasure := h
    simp_rw [e1] at h'
    rw [integral_add i1 i4] at h'
    have e2 : ∫ x, inner ℝ (φ x) (G x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) (f x) ∂cylMeasure - ∫ x, inner ℝ (φ x) (Sη x) ∂cylMeasure := by
      rw [← integral_sub i3 i4]
      refine integral_congr_ae ?_
      filter_upwards [hGae] with x hx
      rw [hx, hg0]
      simp only [inner_sub_right]
    rw [e2, ← h']
    ring
  -- test sections approximating `(η, G)` in the graph norm
  have happ := weak_solution_graph_approx n p hp' η G hw0
  set e : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (1 / ((k : ℝ) + 1)) with he
  have hepos : ∀ k, 0 < e k := fun k => ENNReal.ofReal_pos.2 (by positivity)
  choose u hu hu1 hu2 using fun k : ℕ => happ (e k) (hepos k)
  have he_mono : ∀ k N : ℕ, N ≤ k → e k ≤ e N := by
    intro k N hk
    refine ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity) ?_)
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have he0 : Tendsto e atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    rw [ENNReal.ofReal_zero] at this
    exact this
  -- the estimate at `S∞ = 0`
  obtain ⟨c, hc⟩ := translationInvariant_derivative_estimate n p hp hp' (fun _ => 0)
    continuous_const (fun _ => rfl)
  have hc' : ∀ v : ℝ × ℝ → Vec n, IsTestSection v →
      w1pNorm p v ≤ c * eLpNorm (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) v) p cylMeasure +
        c * eLpNorm v p cylMeasure := fun v hv => hc v hv
  have hD : ∀ k, AEStronglyMeasurable (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) (u k)) cylMeasure :=
    fun k => (c46p_cont_crOp0 (hu k)).aestronglyMeasurable
  set T : ℕ → Triple n p := fun k => testTriple (hu k) with hT
  have hT_mem : ∀ k, T k ∈ W1p p n := fun k =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span (testTriple_mem (hu k)))
  -- Cauchy estimate
  have hdist : ∀ k l N : ℕ, N ≤ k → N ≤ l →
      dist (T k) (T l) ≤ 4 * (c : ℝ) * (1 / ((N : ℝ) + 1)) := by
    intro k l N hk hl
    have hkl := (hu k).sub (hu l)
    have h1 : ENNReal.ofReal ‖T k - T l‖ ≤ w1pNorm p (u k - u l) := by
      refine ofReal_norm_le_w1pNorm ?_ ?_ ?_
      · filter_upwards [Lp.coeFn_sub (T k).1 (T l).1, ((hu k).memLp (p := p)).coeFn_toLp,
          ((hu l).memLp (p := p)).coeFn_toLp] with x h1 h2 h3
        simp only [Prod.fst_sub, Pi.sub_apply] at h1 ⊢
        rw [h1]
        simp only [hT, testTriple, Pi.sub_apply]
        rw [h2, h3]
      · filter_upwards [Lp.coeFn_sub (T k).2.1 (T l).2.1, ((hu k).memLp_partialS (p := p)).coeFn_toLp,
          ((hu l).memLp_partialS (p := p)).coeFn_toLp] with x h1 h2 h3
        simp only [Prod.snd_sub, Prod.fst_sub, Pi.sub_apply] at h1 ⊢
        rw [h1, partialS_sub (hu k) (hu l)]
        simp only [hT, testTriple, Pi.sub_apply]
        rw [h2, h3]
      · filter_upwards [Lp.coeFn_sub (T k).2.2 (T l).2.2, ((hu k).memLp_partialT (p := p)).coeFn_toLp,
          ((hu l).memLp_partialT (p := p)).coeFn_toLp] with x h1 h2 h3
        simp only [Prod.snd_sub, Pi.sub_apply] at h1 ⊢
        rw [h1, partialT_sub (hu k) (hu l)]
        simp only [hT, testTriple, Pi.sub_apply]
        rw [h2, h3]
    have h2 : eLpNorm (u k - u l) p cylMeasure ≤ e k + e l :=
      (c46p_eLpNorm_sub_le (hu k).continuous.aestronglyMeasurable (Lp.aestronglyMeasurable η)
        (hu l).continuous.aestronglyMeasurable).trans (add_le_add (hu1 k) (hu1 l))
    have h3 : eLpNorm (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) (u k - u l)) p cylMeasure ≤ e k + e l := by
      rw [c46p_crOp_sub (hu k) (hu l)]
      exact (c46p_eLpNorm_sub_le (hD k) (Lp.aestronglyMeasurable G) (hD l)).trans
        (add_le_add (hu2 k) (hu2 l))
    have h4 : ENNReal.ofReal ‖T k - T l‖ ≤ (c : ℝ≥0∞) * (e N + e N) + (c : ℝ≥0∞) * (e N + e N) := by
      refine h1.trans ((hc' _ hkl).trans ?_)
      gcongr
      · exact h3.trans (add_le_add (he_mono k N hk) (he_mono l N hl))
      · exact h2.trans (add_le_add (he_mono k N hk) (he_mono l N hl))
    have h5 : (c : ℝ≥0∞) * (e N + e N) + (c : ℝ≥0∞) * (e N + e N) =
        ENNReal.ofReal (4 * (c : ℝ) * (1 / ((N : ℝ) + 1))) := by
      have hc0 : (0 : ℝ) ≤ c := c.coe_nonneg
      have hN : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
      rw [he, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add hN hN,
        ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    rw [h5] at h4
    rw [dist_eq_norm]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4
  have hcauchy : CauchySeq T := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 4 * (c : ℝ) * (1 / ((N : ℝ) + 1)))
      (fun k l N hk hl => hdist k l N hk hl) ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (4 * (c : ℝ))
    rw [mul_zero] at this
    exact this
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hwW : w ∈ W1p p n :=
    (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hw (Eventually.of_forall hT_mem)
  -- `w.1 = η`
  have hw1 : w.1 = η := by
    have h1 : Tendsto (fun k => (T k).1) atTop (𝓝 w.1) := (continuous_fst.tendsto w).comp hw
    have h2 : Tendsto (fun k => (T k).1) atTop (𝓝 η) := by
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he0
        (fun k => bot_le) (fun k => ?_)
      have e1 : eLpNorm (⇑(T k).1 - ⇑η) p cylMeasure = eLpNorm (u k - ⇑η) p cylMeasure := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [((hu k).memLp (p := p)).coeFn_toLp] with x hx
        simp only [Pi.sub_apply, hT, testTriple]
        rw [hx]
      rw [e1]
      exact hu1 k
    exact tendsto_nhds_unique h1 h2
  -- the operator part
  set Jop : LpCyl n p →L[ℝ] LpCyl n p := (matCLM n (J₀ n)).compLpL p cylMeasure with hJop
  set Φ : Triple n p → LpCyl n p := fun v => v.2.1 + Jop v.2.2 with hΦ
  have hΦc : Continuous Φ :=
    (continuous_snd.fst).add (Jop.continuous.comp continuous_snd.snd)
  have hΦae : ∀ v : Triple n p, (Φ v : ℝ × ℝ → Vec n) =ᵐ[cylMeasure]
      fun x => v.2.1 x + Matrix.toEuclideanLin (J₀ n) (v.2.2 x) := by
    intro v
    filter_upwards [Lp.coeFn_add v.2.1 (Jop v.2.2), ContinuousLinearMap.coeFn_compLpL
      (p := p) (μ := cylMeasure) (matCLM n (J₀ n)) v.2.2] with x h1 h2
    rw [hΦ]
    simp only
    rw [h1, Pi.add_apply, hJop, h2, matCLM_apply]
  have hwG : Φ w = G := by
    have h1 : Tendsto (fun k => Φ (T k)) atTop (𝓝 (Φ w)) := (hΦc.tendsto w).comp hw
    have h2 : Tendsto (fun k => Φ (T k)) atTop (𝓝 G) := by
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he0
        (fun k => bot_le) (fun k => ?_)
      have e1 : eLpNorm (⇑(Φ (T k)) - ⇑G) p cylMeasure =
          eLpNorm (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) (u k) - ⇑G) p cylMeasure := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [hΦae (T k), ((hu k).memLp_partialS (p := p)).coeFn_toLp,
          ((hu k).memLp_partialT (p := p)).coeFn_toLp] with x h1 h2 h3
        simp only [Pi.sub_apply]
        rw [h1]
        simp only [hT, testTriple]
        rw [h2, h3]
        simp [crOp]
      rw [e1]
      exact hu2 k
    exact tendsto_nhds_unique h1 h2
  refine ⟨w, hwW, hw1, ?_⟩
  have hGw := hΦae w
  rw [hwG] at hGw
  filter_upwards [hGw, hGae] with x h1 h2
  simp only [crApply]
  rw [hw1, ← h1, h2, hg0, hSη]
  simp only
  abel

end

end CauchyRiemannIndex

-- ===== Scratch/CR46ParentSol.lean =====
open MeasureTheory CauchyRiemannIndex Matrix
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (η f : LpCyl n p)
    (hweak : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (S x)ᵀ (φ x)) (η x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) (f x) ∂cylMeasure) :
    ∃ w ∈ W1p p n, w.1 = η ∧ crApply S w =ᵐ[cylMeasure] (f : ℝ × ℝ → Vec n) :=
  memW1p_aux n p hp hp' Splus Sminus hSplus hSminus S hS η f hweak
