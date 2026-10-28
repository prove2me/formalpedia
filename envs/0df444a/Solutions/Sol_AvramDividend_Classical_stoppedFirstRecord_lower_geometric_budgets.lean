-- Prove2me | solution 1 for AvramDividend.Classical.stoppedFirstRecord_lower_geometric_budgets
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:16:06.457252+00:00
-- url     : https://prove2.me/submissions/f7234201-3d8e-460c-a111-23f8ff89d59f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable
import Theorems.Thm_AvramDividend_Classical_stopped_firstRecord_grid_pathwise_budget
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_expected_scale_lower
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-! The stopped first-record construction follows from pathwise and expectation bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ) (ha : 0 < a)
    (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a) :
    ∃ w : ℕ → Ω → ℝ≥0∞,
      (∀ n : ℕ, AEMeasurable (w n) P) ∧
      (∀ᵐ ω ∂P, (∑' n, w n ω) ≤
        (∫⁻ t, if t ∈ paymentTimes (barrierRuinTime X a ω)
          then ENNReal.ofReal (Real.exp (-(q * t))) else 0
          ∂(dividendMeasure (runningSup X) ω))) ∧
      (∀ n : ℕ,
        ENNReal.ofReal (ε * (W (a - ε) / W a) ^ (n + 1)) ≤
          (∫⁻ ω, w n ω ∂P)) := by
  let w : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
    else 0
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa only [w, zero_add] using
      chat08_record_grid_stopped_weights_aemeasurable
        X a 0 q ε (fun n => n + 1)
  · filter_upwards [] with ω
    have hb : (0 : ℝ) ≤ 0 := le_refl 0
    have hbudget :=
      stopped_firstRecord_grid_pathwise_budget X ω a q 0 ε
        (le_of_lt hq) hb hε
    simpa only [w, zero_add] using hbudget
  · intro n
    have hn :=
      killed_firstRecord_grid_expected_scale_lower
        X hX q hq W hW a ε ha hε hεa hWa hWleft hWinc n
    simpa only [w] using hn
