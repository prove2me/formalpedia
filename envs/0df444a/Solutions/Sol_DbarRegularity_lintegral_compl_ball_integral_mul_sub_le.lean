-- Prove2me | solution 1 for DbarRegularity.lintegral_compl_ball_integral_mul_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:27:40.513568+00:00
-- url     : https://prove2.me/submissions/c9dba2ee-0e70-497b-acd1-55241fb895bf

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal

/-- Off the doubled ball, convolution with a kernel satisfying the Hörmander condition maps a
mean-zero function supported in `closedBall c r` into `L¹` with norm at most `B ‖b‖₁`. -/
theorem lintegral_compl_ball_integral_mul_sub_le {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK : AEStronglyMeasurable K volume) (B : ℝ)
    (hH : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (b : EuclideanSpace ℝ (Fin d) → ℂ) (hb : Integrable b volume) (hb0 : ∫ x, b x = 0)
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (hsupp : ∀ x, b x ≠ 0 → x ∈ closedBall c r) :
    ∫⁻ x in (ball c (2 * r))ᶜ, ‖∫ y, K (x - y) * b y‖ₑ ≤
      ENNReal.ofReal B * eLpNorm b 1 volume := by
  set S : Set (EuclideanSpace ℝ (Fin d)) := (ball c (2 * r))ᶜ with hS
  have hSm : MeasurableSet S := measurableSet_ball.compl
  set F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun x y => ‖K (x - y) - K (x - c)‖ₑ * ‖b y‖ₑ with hF
  -- pointwise bound using the mean-zero condition
  have h1 : ∀ x, ‖∫ y, K (x - y) * b y‖ₑ ≤ ∫⁻ y, F x y := by
    intro x
    by_cases hint : Integrable (fun y => K (x - y) * b y) volume
    · have hz : ∫ y, K (x - c) * b y = 0 := by rw [integral_const_mul, hb0, mul_zero]
      have heq : ∫ y, K (x - y) * b y = ∫ y, (K (x - y) - K (x - c)) * b y := by
        calc ∫ y, K (x - y) * b y = (∫ y, K (x - y) * b y) - ∫ y, K (x - c) * b y := by simp [hz]
          _ = ∫ y, (K (x - y) * b y - K (x - c) * b y) :=
              (integral_sub hint (hb.const_mul _)).symm
          _ = ∫ y, (K (x - y) - K (x - c)) * b y := by congr 1; funext y; ring
      rw [heq]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp [hF, enorm_mul]
    · rw [integral_undef hint]; simp
  -- measurability of the integrand on the product
  have hFm : AEMeasurable (Function.uncurry F) (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖K (p.1 - p.2)‖ₑ) (volume.prod volume) := by
      exact hK.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)
    have h2 : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        K (p.1 - p.2) - K (p.1 - c)) (volume.prod volume) := by
      refine (hK.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)).sub ?_
      exact (hK.comp_quasiMeasurePreserving
        (measurePreserving_sub_right volume c).quasiMeasurePreserving).comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_fst
    exact h2.enorm.mul (hb.1.enorm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hprod : (volume.restrict S).prod (volume : Measure (EuclideanSpace ℝ (Fin d))) =
      (volume.prod volume).restrict (S ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hFmS : AEMeasurable (Function.uncurry F) ((volume.restrict S).prod volume) := by
    rw [hprod]; exact hFm.restrict
  -- inner bound
  have hJ : ∀ y, b y ≠ 0 → ∫⁻ x in S, ‖K (x - y) - K (x - c)‖ₑ ≤ ENNReal.ofReal B := by
    intro y hy
    have hyc : ‖y - c‖ ≤ r := by
      have := hsupp y hy; rwa [mem_closedBall, dist_eq_norm] at this
    rw [← lintegral_indicator hSm]
    rw [← lintegral_add_right_eq_self _ c]
    have hpt : ∀ u, S.indicator (fun x => ‖K (x - y) - K (x - c)‖ₑ) (u + c) =
        {u : EuclideanSpace ℝ (Fin d) | 2 * r ≤ ‖u‖}.indicator
          (fun u => ‖K (u - (y - c)) - K u‖ₑ) u := by
      intro u
      have hmem : (u + c ∈ S) ↔ (2 * r ≤ ‖u‖) := by
        simp [hS, mem_ball, dist_eq_norm, not_lt]
      by_cases h : 2 * r ≤ ‖u‖
      · rw [indicator_of_mem (hmem.2 h), indicator_of_mem (by exact h)]
        congr 2 <;> abel_nf
      · rw [indicator_of_notMem (fun h' => h (hmem.1 h')), indicator_of_notMem (by exact h)]
    simp_rw [hpt]
    rw [lintegral_indicator (measurableSet_le measurable_const measurable_norm)]
    by_cases hyc0 : y - c = 0
    · simp [hyc0]
    · refine le_trans ?_ (hH (y - c) hyc0)
      refine lintegral_mono_set fun u hu => ?_
      simp only [mem_setOf_eq] at hu ⊢
      linarith
  calc ∫⁻ x in S, ‖∫ y, K (x - y) * b y‖ₑ
      ≤ ∫⁻ x in S, ∫⁻ y, F x y := lintegral_mono fun x => h1 x
    _ = ∫⁻ y, ∫⁻ x in S, F x y := lintegral_lintegral_swap hFmS
    _ = ∫⁻ y, ‖b y‖ₑ * ∫⁻ x in S, ‖K (x - y) - K (x - c)‖ₑ := by
        refine lintegral_congr fun y => ?_
        simp only [hF]
        rw [lintegral_mul_const' _ _ enorm_ne_top, mul_comm]
    _ ≤ ∫⁻ y, ‖b y‖ₑ * ENNReal.ofReal B := by
        refine lintegral_mono fun y => ?_
        by_cases hy : b y = 0
        · simp [hy]
        · gcongr; exact hJ y hy
    _ = ENNReal.ofReal B * eLpNorm b 1 volume := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm,
          mul_comm]

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal

theorem solution {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK : AEStronglyMeasurable K volume) (B : ℝ)
    (hH : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (b : EuclideanSpace ℝ (Fin d) → ℂ) (hb : Integrable b volume) (hb0 : ∫ x, b x = 0)
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (hsupp : ∀ x, b x ≠ 0 → x ∈ closedBall c r) :
    ∫⁻ x in (ball c (2 * r))ᶜ, ‖∫ y, K (x - y) * b y‖ₑ ≤
      ENNReal.ofReal B * eLpNorm b 1 volume :=
  lintegral_compl_ball_integral_mul_sub_le K hK B hH b hb hb0 c r hsupp
