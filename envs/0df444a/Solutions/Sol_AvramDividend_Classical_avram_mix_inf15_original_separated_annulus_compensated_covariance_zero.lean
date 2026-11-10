-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:52:45.918438+00:00
-- url     : https://prove2.me/submissions/86160f45-483a-412e-a622-37cd97918f04

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf13_original_threecut_annulus_real_additivity
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_levy_rate_difference
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Compensated counts on any ordered disjoint original annuli are orthogonal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p q : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) (hpq : p ≤ q) :
    let B : ℕ → ℕ → Set ℝ := fun i j =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((j : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i j)
    let r : ℕ → ℕ → ℝ := fun i j =>
      ((T : ℝ≥0∞) * X.ν (B i j)).toReal
    let Y : ℕ → ℕ → Ω → ℝ := fun i j ω => (N i j ω).toReal - r i j
    Integrable (fun ω => Y n m ω * Y p q ω) P ∧
      (∫ ω, Y n m ω * Y p q ω ∂P) = 0 := by
  classical
  let B : ℕ → ℕ → Set ℝ := fun i j =>
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((j : ℝ) + 1)))
  let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B i j)
  let r : ℕ → ℕ → ℝ := fun i j =>
    ((T : ℝ≥0∞) * X.ν (B i j)).toReal
  let Y : ℕ → ℕ → Ω → ℝ := fun i j ω => (N i j ω).toReal - r i j
  change Integrable (fun ω => Y n m ω * Y p q ω) P ∧
    (∫ ω, Y n m ω * Y p q ω ∂P) = 0
  have hLong :=
    avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
      X T n m q hnm (le_trans hmp hpq)
  have hShort :=
    avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
      X T n m p hnm hmp
  change Integrable (fun ω => Y n m ω * Y m q ω) P ∧
    (∫ ω, Y n m ω * Y m q ω ∂P) = 0 at hLong
  change Integrable (fun ω => Y n m ω * Y m p ω) P ∧
    (∫ ω, Y n m ω * Y m p ω ∂P) = 0 at hShort
  let R : ℕ → ℝ := fun j =>
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((j : ℝ) + 1))))).toReal
  have hRP := avram_mixed_source13_original_annulus_levy_rate_difference
    X T m p hmp
  have hRQ := avram_mixed_source13_original_annulus_levy_rate_difference
    X T p q hpq
  have hRMQ := avram_mixed_source13_original_annulus_levy_rate_difference
    X T m q (le_trans hmp hpq)
  change R p = R m + r m p at hRP
  change R q = R p + r p q at hRQ
  change R q = R m + r m q at hRMQ
  have hRate : r m q = r m p + r p q := by linarith
  have hCount := avram_mix_inf13_original_threecut_annulus_real_additivity
    X T m p q hmp hpq
  change ∀ ω, (N m q ω).toReal =
    (N m p ω).toReal + (N p q ω).toReal at hCount
  have hY (ω : Ω) : Y m q ω = Y m p ω + Y p q ω := by
    dsimp [Y]
    rw [hCount ω, hRate]
    ring
  have hProd (ω : Ω) :
      Y n m ω * Y p q ω =
        Y n m ω * Y m q ω - Y n m ω * Y m p ω := by
    rw [hY ω]
    ring
  have hCrossI : Integrable (fun ω => Y n m ω * Y p q ω) P := by
    have heq : (fun ω => Y n m ω * Y p q ω) =
        (fun ω => Y n m ω * Y m q ω - Y n m ω * Y m p ω) := by
      funext ω
      exact hProd ω
    rw [heq]
    exact hLong.1.sub hShort.1
  constructor
  · exact hCrossI
  · calc
      (∫ ω, Y n m ω * Y p q ω ∂P) =
          ∫ ω, Y n m ω * Y m q ω - Y n m ω * Y m p ω ∂P := by
            exact integral_congr_ae (Filter.Eventually.of_forall hProd)
      _ = (∫ ω, Y n m ω * Y m q ω ∂P) -
          (∫ ω, Y n m ω * Y m p ω ∂P) := by
            exact integral_sub hLong.1 hShort.1
      _ = 0 := by rw [hLong.2, hShort.2]; ring
