-- Prove2me | solution 1 for DbarRegularity.eLpNorm_doubleTruncation_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T18:11:36.830901+00:00
-- url     : https://prove2.me/submissions/65cacb20-9a15-4d8a-8d86-0e5e57fd3b4b

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_DbarRegularity_norm_fourier_le_of_hormander
import Theorems.Thm_DbarRegularity_lintegral_indicator_sub_le
import Theorems.Thm_DbarRegularity_memLp_indicator_le_norm
import Theorems.Thm_DbarRegularity_eLpNorm_integral_mul_sub_le_of_hormander
import Theorems.Thm_DbarRegularity_convolution_l2_bound
import Theorems.Thm_DbarRegularity_fourierTransformL2_ae_eq_fourier
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set



namespace DbarRegularity

open MeasureTheory Set Metric FourierTransform
open scoped ENNReal NNReal

/-- For a kernel satisfying Stein's conditions (18)–(19), the operators
`f ↦ ∫ K_{ε,R}(x - y) f(y) dy` with the doubly truncated kernel `K_{ε,R} = K 1_{ε ≤ |x| < R}` are
bounded on `L^1 ∩ L^p`, `1 < p < ∞`, uniformly in `0 < ε` and `0 < R`. -/
theorem eLpNorm_doubleTruncation_le_aux {d : ℕ} (hd : 0 < d) (K : EuclideanSpace ℝ (Fin d) → ℂ)
    (B : ℝ) (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK2 : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ ε R : ℝ, 0 < ε → 0 < R → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ,
      Integrable f volume → MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (fun x => ∫ y, {x | ‖x‖ < R}.indicator ({x | ε ≤ ‖x‖}.indicator K) (x - y) * f y)
          (ENNReal.ofReal p) volume ≤ A * eLpNorm f (ENNReal.ofReal p) volume := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hB : 0 ≤ B := by
    obtain ⟨x, hx⟩ := exists_ne (0 : (EuclideanSpace ℝ (Fin d)))
    have := (norm_nonneg _).trans (hK1 x hx)
    exact (div_nonneg_iff.1 this).elim (fun h => h.1)
      (fun h => absurd h.2 (not_le.2 (by have := norm_pos_iff.2 hx; positivity)))
  obtain ⟨CH, hCH0, hCH⟩ := lintegral_indicator_sub_le hd
  obtain ⟨CF, hCF0, hCF⟩ := norm_fourier_le_of_hormander hd
  set B₁ : ℝ := 2 * (B + CH * B) with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  set M : ℝ := CF * (B + B₁) with hM
  obtain ⟨A, hA⟩ := eLpNorm_integral_mul_sub_le_of_hormander hd p hp B₁.toNNReal M.toNNReal
  refine ⟨A, fun ε R hε hR f hf1 hf => ?_⟩
  set Kε : (EuclideanSpace ℝ (Fin d)) → ℂ := {x | ε ≤ ‖x‖}.indicator K with hKε
  set K' : (EuclideanSpace ℝ (Fin d)) → ℂ := {x | ‖x‖ < R}.indicator Kε with hK'
  have hmeas_le : ∀ r : ℝ, MeasurableSet {x : (EuclideanSpace ℝ (Fin d)) | r ≤ ‖x‖} := fun r =>
    measurableSet_le measurable_const measurable_norm
  have hmeas_lt : ∀ r : ℝ, MeasurableSet {x : (EuclideanSpace ℝ (Fin d)) | ‖x‖ < r} := fun r =>
    measurableSet_lt measurable_norm measurable_const
  have hKε2 : MemLp Kε 2 volume := by
    have := memLp_indicator_le_norm hd K hKm B hK1 ε hε 2 one_lt_two
    simpa using this
  have hK'2 : MemLp K' 2 volume := hKε2.indicator (hmeas_lt R)
  have hK'1 : Integrable K' volume := by
    have hball : {x : (EuclideanSpace ℝ (Fin d)) | ‖x‖ < R} = ball 0 R := by ext x; simp
    rw [hK', hball, integrable_indicator_iff measurableSet_ball]
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : (EuclideanSpace ℝ (Fin d))) R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    exact (hKε2.restrict _).integrable one_le_two
  -- size
  have hsize : ∀ x, x ≠ 0 → ‖K' x‖ ≤ B / ‖x‖ ^ d := by
    intro x hx
    exact (norm_indicator_le_norm_self _ _).trans
      ((norm_indicator_le_norm_self _ _).trans (hK1 x hx))
  -- `K'` as a difference of two outer truncations
  have hdiff : ∀ x, K' x = Kε x - {x | max ε R ≤ ‖x‖}.indicator K x := by
    intro x
    simp only [hK', hKε, indicator, mem_setOf_eq, max_le_iff]
    by_cases h1 : ‖x‖ < R <;> by_cases h2 : ε ≤ ‖x‖
    · simp [h1, h2, not_le.2 h1]
    · simp [h1, h2]
    · simp [h1, h2, not_lt.1 h1]
    · simp [h1, h2]
  -- Hörmander
  have hHorm : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K' (x - y) - K' x‖ₑ ≤
      ENNReal.ofReal B₁ := by
    intro y hy
    set Km : (EuclideanSpace ℝ (Fin d)) → ℂ := {x | max ε R ≤ ‖x‖}.indicator K
    have hKεm : AEStronglyMeasurable Kε volume := hKm.indicator (hmeas_le ε)
    have hpt : ∀ x, ‖K' (x - y) - K' x‖ₑ ≤
        ‖Kε (x - y) - Kε x‖ₑ + ‖Km (x - y) - Km x‖ₑ := by
      intro x
      rw [hdiff, hdiff]
      calc ‖Kε (x - y) - Km (x - y) - (Kε x - Km x)‖ₑ
          = ‖(Kε (x - y) - Kε x) - (Km (x - y) - Km x)‖ₑ := by ring_nf
        _ ≤ _ := enorm_sub_le
    have hae : AEMeasurable (fun x => ‖Kε (x - y) - Kε x‖ₑ)
        (volume.restrict {x : (EuclideanSpace ℝ (Fin d)) | 2 * ‖y‖ ≤ ‖x‖}) :=
      (((hKεm.comp_measurePreserving (measurePreserving_sub_right volume y)).sub
        hKεm).enorm).restrict
    calc _ ≤ ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, (‖Kε (x - y) - Kε x‖ₑ + ‖Km (x - y) - Km x‖ₑ) :=
          lintegral_mono hpt
      _ = (∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖Kε (x - y) - Kε x‖ₑ) +
            ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖Km (x - y) - Km x‖ₑ := lintegral_add_left' hae _
      _ ≤ (ENNReal.ofReal B + ENNReal.ofReal (CH * B)) +
            (ENNReal.ofReal B + ENNReal.ofReal (CH * B)) := by
          refine add_le_add ?_ ?_
          · exact (hCH K B hK1 ε hε y).trans (add_le_add (hK2 y hy) le_rfl)
          · exact (hCH K B hK1 (max ε R) (lt_max_of_lt_left hε) y).trans
              (add_le_add (hK2 y hy) le_rfl)
      _ = ENNReal.ofReal B₁ := by
          rw [← ENNReal.ofReal_add hB (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), hB₁]
          congr 1; ring
  -- cancellation on balls
  have hzero : ∀ r : ℝ, 0 < r → ∫ x in ball (0 : (EuclideanSpace ℝ (Fin d))) r, K' x = 0 := by
    intro r hr
    rw [hK', setIntegral_indicator (hmeas_lt R), hKε, setIntegral_indicator (hmeas_le ε)]
    set m := min r R
    have hset : ball (0 : (EuclideanSpace ℝ (Fin d))) r ∩ {x | ‖x‖ < R} ∩ {x | ε ≤ ‖x‖} =
        {x | ε ≤ ‖x‖ ∧ ‖x‖ < m} := by
      ext x; simp only [mem_inter_iff, mem_ball_zero_iff, mem_setOf_eq, m, lt_min_iff]; tauto
    rw [hset]
    have hae : {x : (EuclideanSpace ℝ (Fin d)) | ε ≤ ‖x‖ ∧ ‖x‖ < m} =ᵐ[volume] {x : (EuclideanSpace ℝ (Fin d)) | ε < ‖x‖ ∧ ‖x‖ < m} := by
      refine (ae_eq_set).2 ⟨?_, ?_⟩
      · refine measure_mono_null (t := sphere (0 : (EuclideanSpace ℝ (Fin d))) ε) ?_ (Measure.addHaar_sphere _ _ _)
        intro x hx
        simp only [mem_diff, mem_setOf_eq, not_and, not_lt] at hx
        simp only [mem_sphere_zero_iff_norm]
        by_contra hne
        have h' : ε < ‖x‖ := lt_of_le_of_ne hx.1.1 (Ne.symm hne)
        exact absurd hx.1.2 (not_lt.2 (hx.2 h'))
      · have : {x : (EuclideanSpace ℝ (Fin d)) | ε < ‖x‖ ∧ ‖x‖ < m} \ {x : (EuclideanSpace ℝ (Fin d)) | ε ≤ ‖x‖ ∧ ‖x‖ < m} = ∅ := by
          ext x
          simp only [mem_diff, mem_setOf_eq, mem_empty_iff_false, iff_false]
          rintro ⟨⟨h1, h2⟩, h3⟩
          exact h3 ⟨h1.le, h2⟩
        rw [this, measure_empty]
    rw [setIntegral_congr_set hae]
    by_cases hεm : ε < m
    · exact hK3 ε m hε hεm
    · have : {x : (EuclideanSpace ℝ (Fin d)) | ε < ‖x‖ ∧ ‖x‖ < m} = ∅ := by
        ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
        intro h; linarith [not_lt.1 hεm]
      rw [this, Measure.restrict_empty, integral_zero_measure]
  -- Fourier bound and `L²` bound
  have hFT : ∀ ξ, ‖𝓕 K' ξ‖ ≤ M := hCF K' B B₁ hB₁0 hK'1 hsize hHorm hzero
  have hFT2 : ∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK'2.toLp K') ξ‖ ≤ M := by
    filter_upwards [fourierTransformL2_ae_eq_fourier K' hK'1 hK'2] with ξ hξ
    rw [hξ]; exact hFT ξ
  have hL2 : ∀ g : (EuclideanSpace ℝ (Fin d)) → ℂ, MemLp g 2 volume →
      eLpNorm (fun x => ∫ y, K' (x - y) * g y) 2 volume ≤ (M.toNNReal : ℝ≥0∞) * eLpNorm g 2 volume :=
    fun g hg => (convolution_l2_bound K' hK'2 M hFT2 g hg).2
  exact hA K' hK'2 (fun y hy => hHorm y hy) hL2 f hf1 hf

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal NNReal

theorem solution {d : ℕ} (hd : 0 < d) (K : EuclideanSpace ℝ (Fin d) → ℂ)
    (B : ℝ) (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK2 : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ ε R : ℝ, 0 < ε → 0 < R → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ,
      Integrable f volume → MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (fun x => ∫ y, {x | ‖x‖ < R}.indicator ({x | ε ≤ ‖x‖}.indicator K) (x - y) * f y)
          (ENNReal.ofReal p) volume ≤ A * eLpNorm f (ENNReal.ofReal p) volume :=
  DbarRegularity.eLpNorm_doubleTruncation_le_aux hd K B hKm hK1 hK2 hK3 p hp
