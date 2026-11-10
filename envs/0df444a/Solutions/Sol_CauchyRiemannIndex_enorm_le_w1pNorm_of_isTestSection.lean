-- Prove2me | solution 1 for CauchyRiemannIndex.enorm_le_w1pNorm_of_isTestSection
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T16:39:47.410469+00:00
-- url     : https://prove2.me/submissions/f171702c-47ce-4c1e-95ac-46207df10902

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Theorems.Thm_JHolomorphic_enorm_sub_le_of_contDiffOn_ball
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls



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

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

variable {n : ℕ}

lemma norm_fderiv_le_partialS_add_partialT (u : ℝ × ℝ → Vec n) (y : ℝ × ℝ) :
    ‖fderiv ℝ u y‖ ≤ ‖partialS u y‖ + ‖partialT u y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hv, map_add, map_smul, map_smul]
  calc ‖v.1 • fderiv ℝ u y (1, 0) + v.2 • fderiv ℝ u y (0, 1)‖
      ≤ ‖v.1‖ * ‖partialS u y‖ + ‖v.2‖ * ‖partialT u y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]; rfl
    _ ≤ ‖v‖ * ‖partialS u y‖ + ‖v‖ * ‖partialT u y‖ := by
        gcongr
        · exact norm_fst_le v
        · exact norm_snd_le v
    _ = (‖partialS u y‖ + ‖partialT u y‖) * ‖v‖ := by ring

lemma norm_equivRealProdCLM_le :
    ‖(Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  change ‖(z.re, z.im)‖ ≤ ‖z‖
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)

/-- The bound at points `(s, t)` with `0 < t < 1`. -/
lemma enorm_le_w1pNorm_of_mem_Ioo (p : ℝ≥0∞) (hp : 2 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : ℝ × ℝ → Vec n, IsTestSection u → ∀ s t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖u (s, t)‖ₑ ≤ C * w1pNorm p u := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp.le
  have hp0 : p ≠ 0 := by positivity
  have hpr : 2 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (by norm_num) hp').2 hp
    simpa using this
  have hpofr : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hp'
  obtain ⟨CM, hCM⟩ := JHolomorphic.enorm_sub_le_of_contDiffOn_ball (E := Vec n) p.toReal hpr
  set m : ℝ≥0∞ := ENNReal.ofReal (1 / 2) ^ 2 * NNReal.pi with hm
  have hm0 : m ≠ 0 := by
    rw [hm]; refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · simp
    · simp [NNReal.pi_ne_zero]
  have hmT : m ≠ ⊤ := by rw [hm]; exact ENNReal.mul_ne_top (by simp) (by simp)
  set a : ℝ≥0∞ := m ^ p.toReal⁻¹ with ha
  have hpinv : 0 < p.toReal⁻¹ := inv_pos.2 (by linarith)
  have ha0 : a ≠ 0 := by
    rw [ha]; exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 hm0) hmT).ne'
  have haT : a ≠ ⊤ := by rw [ha]; exact ENNReal.rpow_ne_top_of_nonneg hpinv.le hmT
  set K0 : ℝ≥0∞ := ENNReal.ofReal (CM * (1 / 2) ^ (1 - 2 / p.toReal)) with hK0
  refine ⟨a⁻¹ + K0, ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 ha0, ENNReal.ofReal_ne_top⟩, ?_⟩
  intro u hu s t ht
  set e : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM with he
  have hmp : MeasurePreserving (e : ℂ → ℝ × ℝ) volume volume :=
    Complex.volume_preserving_equiv_real_prod
  set c : ℂ := ⟨s, 1 / 2⟩ with hc
  set z0 : ℂ := ⟨s, t⟩ with hz0
  have hz0B : z0 ∈ ball c (1 / 2) := by
    rw [mem_ball]
    have hre : z0.re = c.re := rfl
    rw [Complex.dist_of_re_eq hre, Real.dist_eq, abs_lt]
    change -(1 / 2) < t - 1 / 2 ∧ t - 1 / 2 < 1 / 2
    constructor <;> linarith [ht.1, ht.2]
  set F : ℂ → Vec n := u ∘ (e : ℂ → ℝ × ℝ) with hF
  have hFsmooth : ContDiff ℝ ∞ F := hu.1.comp e.contDiff
  have hFon : ContDiffOn ℝ 1 F (ball c (1 / 2)) := (hFsmooth.of_le (by simp)).contDiffOn
  have hFc : Continuous F := hFsmooth.continuous
  set μ : Measure ℂ := volume.restrict (ball c (1 / 2)) with hμ
  have hμuniv : μ univ = m := by
    rw [hμ, Measure.restrict_apply_univ, Complex.volume_ball]
  have hμ0 : μ ≠ 0 := by
    intro h; apply hm0; rw [← hμuniv, h]; rfl
  set K : ℝ≥0∞ := K0 * eLpNorm (fderiv ℝ F) p μ with hK
  -- pointwise oscillation
  have hosc : ∀ᵐ y ∂μ, ‖F z0 - F y‖ₑ ≤ K := by
    refine ae_restrict_of_forall_mem measurableSet_ball fun y hy => ?_
    have := hCM c (1 / 2) (by norm_num) F hFon z0 hz0B y hy
    rwa [hpofr] at this
  have hsplit : (fun _ : ℂ => F z0) = F + fun y => F z0 - F y := by
    funext y; simp
  have hconst : eLpNorm (fun _ : ℂ => F z0) p μ = ‖F z0‖ₑ * a := by
    rw [eLpNorm_const _ hp0 hμ0, hμuniv, ha, one_div]
  have hmain : ‖F z0‖ₑ * a ≤ eLpNorm F p μ + K * a := by
    rw [← hconst, hsplit]
    refine (eLpNorm_add_le hFc.aestronglyMeasurable
      (continuous_const.sub hFc).aestronglyMeasurable hp1).trans ?_
    gcongr
    refine (eLpNorm_le_of_ae_enorm_bound hosc).trans_eq ?_
    rw [hμuniv, smul_eq_mul, ha]
  have hpt : ‖F z0‖ₑ ≤ a⁻¹ * eLpNorm F p μ + K := by
    have h1 : ‖F z0‖ₑ = ‖F z0‖ₑ * a * a⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel ha0 haT, mul_one]
    rw [h1]
    calc ‖F z0‖ₑ * a * a⁻¹ ≤ (eLpNorm F p μ + K * a) * a⁻¹ := by gcongr
      _ = a⁻¹ * eLpNorm F p μ + K := by
        rw [add_mul, mul_assoc, ENNReal.mul_inv_cancel ha0 haT, mul_one, mul_comm]
  -- transfer to the strip
  set S' : Set (ℝ × ℝ) := (e.symm : ℝ × ℝ → ℂ) ⁻¹' ball c (1 / 2) with hS'
  have hS'm : MeasurableSet S' := (isOpen_ball.preimage e.symm.continuous).measurableSet
  have hpre : (e : ℂ → ℝ × ℝ) ⁻¹' S' = ball c (1 / 2) := by
    ext z; simp [hS']
  have hmpS : MeasurePreserving (e : ℂ → ℝ × ℝ) μ (volume.restrict S') := by
    have := hmp.restrict_preimage hS'm
    rwa [hpre] at this
  have hS'sub : S' ⊆ univ ×ˢ Ico (0 : ℝ) 1 := by
    intro y hy
    simp only [hS', mem_preimage, mem_ball, Complex.dist_eq] at hy
    have him := (Complex.abs_im_le_norm _).trans_lt hy
    rw [Complex.equivRealProdCLM_symm_apply] at him
    simp only [hc, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add] at him
    rw [abs_lt] at him
    exact ⟨mem_univ _, by linarith, by linarith⟩
  have hle : volume.restrict S' ≤ cylMeasure := by
    unfold cylMeasure; exact Measure.restrict_mono hS'sub le_rfl
  have hF1 : eLpNorm F p μ ≤ eLpNorm u p cylMeasure := by
    rw [hF, eLpNorm_comp_measurePreserving hu.continuous.aestronglyMeasurable hmpS]
    exact eLpNorm_mono_measure _ hle
  set G : ℝ × ℝ → ℝ := fun y => ‖partialS u y‖ + ‖partialT u y‖ with hG
  have hGc : Continuous G := hu.continuous_partialS.norm.add hu.continuous_partialT.norm
  have hdF : ∀ z, ‖fderiv ℝ F z‖ ≤ ‖(G ∘ (e : ℂ → ℝ × ℝ)) z‖ := by
    intro z
    rw [hF, ContinuousLinearEquiv.comp_right_fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [Function.comp_apply, Real.norm_of_nonneg (by positivity)]
    calc ‖fderiv ℝ u (e z)‖ * ‖(e : ℂ →L[ℝ] ℝ × ℝ)‖ ≤ ‖fderiv ℝ u (e z)‖ * 1 := by
          gcongr; exact norm_equivRealProdCLM_le
      _ ≤ G (e z) := by rw [mul_one]; exact norm_fderiv_le_partialS_add_partialT u (e z)
  have hF2 : eLpNorm (fderiv ℝ F) p μ ≤
      eLpNorm (partialS u) p cylMeasure + eLpNorm (partialT u) p cylMeasure := by
    refine (eLpNorm_mono hdF).trans ?_
    rw [eLpNorm_comp_measurePreserving hGc.aestronglyMeasurable hmpS]
    refine (eLpNorm_mono_measure _ hle).trans ?_
    refine (eLpNorm_add_le hu.continuous_partialS.norm.aestronglyMeasurable
      hu.continuous_partialT.norm.aestronglyMeasurable hp1).trans ?_
    rw [eLpNorm_norm, eLpNorm_norm]
  have hFz : F z0 = u (s, t) := rfl
  rw [← hFz]
  refine hpt.trans ?_
  unfold w1pNorm
  set A := eLpNorm u p cylMeasure
  set B := eLpNorm (partialS u) p cylMeasure
  set D := eLpNorm (partialT u) p cylMeasure
  calc a⁻¹ * eLpNorm F p μ + K ≤ a⁻¹ * A + K0 * (B + D) := by
        rw [hK]; gcongr
    _ ≤ (a⁻¹ + K0) * A + (a⁻¹ + K0) * (B + D) := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = (a⁻¹ + K0) * (A + B + D) := by rw [← mul_add, add_assoc]

/-- Pointwise bound of a test section by its `W^{1,p}` norm, for `2 < p < ∞`. -/
theorem enorm_le_w1pNorm_of_isTestSection_aux (p : ℝ≥0∞) (hp : 2 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, ∀ u : ℝ × ℝ → Vec n, IsTestSection u → ∀ x : ℝ × ℝ,
      ‖u x‖ₑ ≤ ENNReal.ofReal C * w1pNorm p u := by
  obtain ⟨C, hCT, hC⟩ := enorm_le_w1pNorm_of_mem_Ioo (n := n) p hp hp'
  refine ⟨C.toReal, fun u hu x => ?_⟩
  rw [ENNReal.ofReal_toReal hCT]
  obtain ⟨s, t⟩ := x
  have hper : Function.Periodic (fun t => u (s, t)) 1 := fun t => hu.2.1 s t
  have hcl : IsClosed {t : ℝ | ‖u (s, t)‖ₑ ≤ C * w1pNorm p u} :=
    isClosed_le ((hu.continuous.comp (Continuous.prodMk_right s)).enorm) continuous_const
  have hIcc : Icc (0 : ℝ) 1 ⊆ {t : ℝ | ‖u (s, t)‖ₑ ≤ C * w1pNorm p u} := by
    rw [← closure_Ioo zero_ne_one]
    exact closure_minimal (fun t ht => hC u hu s t ht) hcl
  have hfr : u (s, t) = u (s, Int.fract t) := by
    have := hper.sub_int_mul_eq (x := t) ⌊t⌋
    rw [mul_one] at this
    rw [Int.fract]; exact this.symm
  rw [hfr]
  exact hIcc ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal NNReal

theorem solution {n : ℕ} (p : ℝ≥0∞) (hp : 2 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, ∀ u : ℝ × ℝ → Vec n, IsTestSection u → ∀ x : ℝ × ℝ,
      ‖u x‖ₑ ≤ ENNReal.ofReal C * w1pNorm p u :=
  enorm_le_w1pNorm_of_isTestSection_aux p hp hp'
