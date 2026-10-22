-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_le_of_hjb
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T01:42:32.345993+00:00
-- url     : https://prove2.me/submissions/25552412-0f39-48a5-a167-166ec8df36f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_bounded_variation
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/--
The expected discounted dividends paid by a fixed admissible strategy are
bounded by the initial verification value.

## The route

The value of a fixed strategy is the supremum over the integer horizons of
the truncated expected discounted dividends, by the Proved
`dividendValue_eq_iSup_truncated` (`3b737955`).  Each truncated horizon is
bounded by the initial verification value in the two regularity branches:

* bounded variation - `admissible_cap_truncated_dividendValue_le_bounded_variation`
  (`e068df0b`);
* unbounded variation - `admissible_cap_truncated_dividendValue_le_unbounded_variation`
  (`cc518136`).

Each of those two children is the same statement as the present target with
the horizon `T` made explicit and the value taken at a single truncation;
they are the genuine analytic input of Proposition 4(i) and are still
**Open**, so this source is a source-faithful reduction of the target onto
them.

The smoothness hypothesis of the present target is a disjunction, so the
bounded-variation branch of it is used in the bounded-variation case and
the unbounded-variation branch in the unbounded-variation case.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  -- The truncated bounds, one per regularity branch.
  have htrunc : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
    intro n
    by_cases hBV : X.BoundedVariation
    · exact admissible_cap_truncated_dividendValue_le_bounded_variation
        X hX hBV q hq w C hC hw_cont hw0 hw_neg (hw_smooth.2 hBV)
        hw_hjb x hx hxc D hD (n : ℝ) (by norm_num)
    · exact admissible_cap_truncated_dividendValue_le_unbounded_variation
        X hX hBV q hq w C hC hw_cont hw0 hw_neg (hw_smooth.1 hBV)
        hw_hjb x hx hxc D hD (n : ℝ) (by norm_num)
  -- The value is the supremum of the truncated expectations.
  rw [dividendValue_eq_iSup_truncated X q x D hD.1]
  exact iSup_le htrunc
