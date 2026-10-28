-- Prove2me | solution 1 for AvramDividend.Classical.bounded_variation_stopped_scale_balance
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:30:51.254586+00:00
-- url     : https://prove2.me/submissions/eacc0d0d-4893-49e8-8cb3-807594ffa441
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- REPAIR ITERATION N of CE 16458 (E01 TACTIC_FAILURE measurability, E02 TYPE_MISMATCH lintegral_mul_const).
-- Cause-linked hypothesis vs M: `measurability` cannot discharge exit-clock measurability
-- (uncountable-inf clocks; aesop exhausted), and `lintegral_mul_const _ hMeas` was applied to an
-- ite-with-inner-mul integrand that does not unify with `fun a => f a * r` (first diff token ?m.282 vs P).
-- Repair: (1) cite Proved 065fe2d0 (chat03_exact_upperfirst_discount_integrand_measurable) for the exact
-- integrand measurability -- no new measurability proof; (2) insert pointwise funext/by_cases equality
-- before factoring so the lemma unifies; (3) keep single Open premise 09caed2c (honest sketch reduction).
-- Sorry-free; expected SKETCH_ACCEPTED (Open premise) or a precise new-bridge CE.
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_payoff_balance
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  have hChild : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
      else 0 ∂P) = ENNReal.ofReal (W x) :=
    AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
      X hX q hq W hW hBV a x ha hx0 hxa
  have hMeas : Measurable (fun ω =>
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
      else 0) :=
    AvramDividend.Classical.chat03_exact_upperfirst_discount_integrand_measurable
      X (-x) (a - x) q
  have hEq : (fun ω => if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
      else 0)
      = (fun ω => ((if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
      else 0) * ENNReal.ofReal (W a))) := by
    funext ω
    by_cases h : twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω <;> simp [h]
  have hFact : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
      else 0 ∂P)
      = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
      else 0 ∂P) * ENNReal.ofReal (W a) := by
    rw [hEq]
    exact MeasureTheory.lintegral_mul_const _ hMeas
  rw [hFact] at hChild
  have hBridge : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P)
      = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
      else 0 ∂P) := by
    rfl
  rw [hBridge, hChild]
