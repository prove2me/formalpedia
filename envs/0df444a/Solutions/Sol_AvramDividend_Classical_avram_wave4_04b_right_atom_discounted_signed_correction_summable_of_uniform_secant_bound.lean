-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_right_atom_discounted_signed_correction_summable_of_uniform_secant_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:56:16.703078+00:00
-- url     : https://prove2.me/submissions/2b59c487-5f85-4115-ab54-90d935707bd5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- Actual finite-horizon dividend atom-mass summability, together with a
uniform localized secant growth bound, forces absolute convergence of the
discounted chronological signed right-payment corrections. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (A : Set ℝ) (hA : A.Countable)
    (hAnonneg : ∀ s : A, (0 : ℝ) ≤ (s : ℝ))
    (hq : 0 ≤ q)
    (L : ℝ) (hL : 0 ≤ L)
    (hMass : Summable (fun s : A => (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(s : ℝ)}).toReal))
    (hSecantBound : ∀ s : A, |((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))| ≤ L * (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(s : ℝ)}).toReal) :
    Summable (fun s : A => Real.exp (-(q * (s : ℝ))) * ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))) := by
  have hWeighted : Summable (fun s : A => L * (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(s : ℝ)}).toReal) :=
    hMass.mul_left L
  apply Summable.of_norm_bounded hWeighted
  intro s
  have hs : 0 ≤ (s : ℝ) := hAnonneg s
  have hExpPos : 0 ≤ Real.exp (-(q * (s : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have hExpLe : Real.exp (-(q * (s : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hqtime : 0 ≤ q * (s : ℝ) := mul_nonneg hq hs
    linarith
  calc
    ‖Real.exp (-(q * (s : ℝ))) * ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))‖ = Real.exp (-(q * (s : ℝ))) * |((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hExpPos]
    _ ≤ 1 * |((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))| := by
      exact mul_le_mul_of_nonneg_right hExpLe (abs_nonneg _)
    _ = |((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))| := by ring
    _ ≤ L * (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(s : ℝ)}).toReal := hSecantBound s
