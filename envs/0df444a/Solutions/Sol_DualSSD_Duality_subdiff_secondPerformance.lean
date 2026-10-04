-- Prove2me | solution 1 for DualSSD.Duality.subdiff_secondPerformance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:30:03.691681+00:00
-- url     : https://prove2.me/submissions/dac773de-0d21-47ab-96bc-cada0c463d23

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance
import Definitions.Def_DualSSD_Duality_conj

set_option autoImplicit false

open MeasureTheory in
theorem sd4_shift (c : ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    ∫ u in S, f u = ∫ t in (fun t : ℝ => t + c) ⁻¹' S, f (t + c) := by
  have A : MeasurableEmbedding (fun t : ℝ => t + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have h := A.setIntegral_map (μ := volume) f S
  rw [map_add_right_eq_self] at h
  exact h

open MeasureTheory Filter in
/-- Layer cake: the second performance function is the expected shortfall `E (η - X)⁺`. -/
theorem sd4_perf_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (x : ℝ) :
    DualSSD.Shared.secondPerformance μ X x = ∫ ω, max (x - X ω) 0 ∂μ := by
  have hi : Integrable (fun ω => max (x - X ω) 0) μ := ((integrable_const x).sub hX).pos_part
  rw [DualSSD.Shared.secondPerformance,
    hi.integral_eq_integral_meas_le (Eventually.of_forall fun ω => le_max_right _ _),
    sd4_shift x (DualSSD.Shared.distFun μ X) (Set.Iic x), Set.preimage_add_const_Iic, sub_self]
  have h2 := integral_comp_neg_Ioi (0 : ℝ) (fun s => DualSSD.Shared.distFun μ X (s + x))
  rw [neg_zero] at h2
  rw [← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [DualSSD.Shared.distFun, measureReal_def]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, le_max_iff]
  have ht' : 0 < t := ht
  constructor
  · intro h; left; linarith
  · rintro (h | h)
    · linarith
    · linarith

open Set in
theorem sd4_pt (a b y : ℝ) (hab : a ≤ b) :
    (b - a) * (Iic a).indicator (1 : ℝ → ℝ) y ≤ max (b - y) 0 - max (a - y) 0 ∧
      max (b - y) 0 - max (a - y) 0 ≤ (b - a) * (Iio b).indicator (1 : ℝ → ℝ) y := by
  by_cases h1 : y ≤ a
  · rw [indicator_of_mem (show y ∈ Iic a from h1), max_eq_left (by linarith : (0:ℝ) ≤ a - y)]
    by_cases h2 : y < b
    · rw [indicator_of_mem (show y ∈ Iio b from h2), max_eq_left (by linarith : (0:ℝ) ≤ b - y)]
      simp only [Pi.one_apply, mul_one]
      constructor <;> linarith
    · rw [indicator_of_notMem (show y ∉ Iio b from h2), max_eq_left (by linarith : (0:ℝ) ≤ b - y)]
      have hb : b ≤ y := not_lt.mp h2
      simp only [Pi.one_apply, mul_one, mul_zero]
      constructor <;> linarith
  · have h1' : a < y := not_le.mp h1
    rw [indicator_of_notMem (show y ∉ Iic a from h1), max_eq_right (by linarith : a - y ≤ 0)]
    by_cases h2 : y < b
    · rw [indicator_of_mem (show y ∈ Iio b from h2), max_eq_left (by linarith : (0:ℝ) ≤ b - y)]
      simp only [Pi.one_apply, mul_one, mul_zero]
      constructor <;> linarith
    · rw [indicator_of_notMem (show y ∉ Iio b from h2),
        max_eq_right (by linarith [not_lt.mp h2] : b - y ≤ 0)]
      simp

open MeasureTheory Set in
theorem sd4_diff (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable (fun y : ℝ => y) μ)
    {a b : ℝ} (hab : a ≤ b) :
    (b - a) * μ.real (Iic a) ≤ (∫ y, max (b - y) 0 ∂μ) - ∫ y, max (a - y) 0 ∂μ ∧
      (∫ y, max (b - y) 0 ∂μ) - ∫ y, max (a - y) 0 ∂μ ≤ (b - a) * μ.real (Iio b) := by
  have hib : Integrable (fun y : ℝ => max (b - y) 0) μ := ((integrable_const b).sub hμ).pos_part
  have hia : Integrable (fun y : ℝ => max (a - y) 0) μ := ((integrable_const a).sub hμ).pos_part
  have hI : ∀ s : Set ℝ, MeasurableSet s →
      Integrable (fun y => (b - a) * s.indicator (1 : ℝ → ℝ) y) μ :=
    fun s hs => ((integrable_const (1:ℝ)).indicator hs).const_mul (b - a)
  rw [← integral_sub hib hia, ← integral_indicator_one measurableSet_Iic,
    ← integral_indicator_one measurableSet_Iio, ← integral_const_mul, ← integral_const_mul]
  constructor
  · exact integral_mono (hI _ measurableSet_Iic) (hib.sub hia) (fun y => (sd4_pt a b y hab).1)
  · exact integral_mono (hib.sub hia) (hI _ measurableSet_Iio) (fun y => (sd4_pt a b y hab).2)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem sd4_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable (fun y : ℝ => y) μ)
    (η : ℝ) :
    DualSSD.Duality.subdiff (fun c => ∫ y, max (c - y) 0 ∂μ) η =
      Icc (μ.real (Iio η)) (μ.real (Iic η)) := by
  have hF : ∀ t, μ.real (Iic t) = cdf μ t := fun t => (cdf_eq_real μ t).symm
  have hL : μ.real (Iio η) = Function.leftLim (cdf μ) η := by
    have hm := StieltjesFunction.measure_Iio (f := cdf μ) (tendsto_cdf_atBot μ) η
    rw [measure_cdf] at hm
    rw [measureReal_def, hm, sub_zero]
    apply ENNReal.toReal_ofReal
    exact le_trans (cdf_nonneg μ (η - 1)) (Monotone.le_leftLim (monotone_cdf μ) (by linarith))
  ext g
  simp only [DualSSD.Duality.subdiff, mem_setOf_eq, mem_Icc]
  constructor
  · intro hg
    constructor
    · rw [hL, Monotone.leftLim_eq_sSup (monotone_cdf μ)]
      apply csSup_le (Set.Nonempty.image _ ⟨η - 1, by simp⟩)
      rintro _ ⟨t, ht, rfl⟩
      have ht' : t < η := ht
      have h1 := (sd4_diff μ hμ ht'.le).1
      have h2 := hg t
      rw [← hF]
      have h3 : (η - t) * μ.real (Iic t) ≤ (η - t) * g := by linarith
      exact le_of_mul_le_mul_left h3 (by linarith)
    · rw [hF]
      have hrc : ContinuousWithinAt (cdf μ) (Ioi η) η :=
        ((cdf μ).right_continuous η).mono Ioi_subset_Ici_self
      apply ge_of_tendsto hrc
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : η < t := ht
      have h1 := (sd4_diff μ hμ ht'.le).2
      have h2 := hg t
      have h4 : μ.real (Iio t) ≤ μ.real (Iic t) := measureReal_mono Iio_subset_Iic_self
      rw [← hF]
      have h3 : (t - η) * g ≤ (t - η) * μ.real (Iic t) := by nlinarith
      exact le_of_mul_le_mul_left h3 (by linarith)
  · rintro ⟨hg1, hg2⟩ ξ
    rcases le_total η ξ with h | h
    · have h1 := (sd4_diff μ hμ h).1
      have h3 : g * (ξ - η) ≤ μ.real (Iic η) * (ξ - η) :=
        mul_le_mul_of_nonneg_right hg2 (by linarith)
      linarith
    · have h1 := (sd4_diff μ hμ h).2
      have h3 : μ.real (Iio η) * (η - ξ) ≤ g * (η - ξ) :=
        mul_le_mul_of_nonneg_right hg1 (by linarith)
      linarith

open MeasureTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) :
    DualSSD.Duality.subdiff (DualSSD.Shared.secondPerformance P X) η =
      Set.Icc (P.real {ω | X ω < η}) (P.real {ω | X ω ≤ η}) := by
  have hXm := hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hXm
  have hμ : Integrable (fun y : ℝ => y) (P.map X) :=
    (integrable_map_measure aestronglyMeasurable_id hXm).mpr hX
  have hfun : DualSSD.Shared.secondPerformance P X
      = fun c => ∫ y, max (c - y) 0 ∂(P.map X) := by
    funext c
    rw [sd4_perf_eq P X hX c,
      integral_map hXm (by fun_prop : Continuous fun y : ℝ => max (c - y) 0).aestronglyMeasurable]
  have h1 : P.real {ω | X ω < η} = (P.map X).real (Set.Iio η) := by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable hXm measurableSet_Iio]
    rfl
  have h2 : P.real {ω | X ω ≤ η} = (P.map X).real (Set.Iic η) := by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable hXm measurableSet_Iic]
    rfl
  rw [hfun, h1, h2]
  exact sd4_core (P.map X) hμ η
