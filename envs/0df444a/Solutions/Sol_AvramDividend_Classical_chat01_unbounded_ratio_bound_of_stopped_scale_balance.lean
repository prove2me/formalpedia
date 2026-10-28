-- Prove2me | solution 1 for AvramDividend.Classical.chat01_unbounded_ratio_bound_of_stopped_scale_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T12:03:22.76763+00:00
-- url     : https://prove2.me/submissions/f65dd19e-a35a-40ab-9a71-75f75c48952b

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_esscher_decay_of_stopped_scale_balance
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_tilted_scale_mono_of_stopped_balance
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The corrected stopped-scale balance implies the exact positive-root
    ratio estimate, including positivity of the denominator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hBalance : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    ∃ (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q),
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-(φ * (y - x))) := by
  rcases chat01_unbounded_tilted_scale_mono_of_stopped_balance
      X q hq W hW hnbv hBalance with ⟨hpos, φ, hφ, hroot, _⟩
  refine ⟨φ, hφ, hroot, ?_⟩
  intro x y hx hxy
  have hy : 0 < W y := hpos y (lt_of_lt_of_le hx hxy)
  have hbound := chat01_unbounded_esscher_decay_of_stopped_scale_balance
    X q hq W hW hnbv φ hφ hroot hBalance x y hx hxy
  exact (div_le_iff₀ hy).2 hbound
