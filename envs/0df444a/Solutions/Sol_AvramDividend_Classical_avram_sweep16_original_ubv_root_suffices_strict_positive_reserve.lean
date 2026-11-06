-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_ubv_root_suffices_strict_positive_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:47:36.440678+00:00
-- url     : https://prove2.me/submissions/aa3e8f76-30ce-4576-b6b6-70ac746de42d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_complete_root_at_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- Root in unbounded variation reduces exactly to strict positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hCapPositive : ∀ x : ℝ, 0 < x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x))
    (hTopPositive :
      (∀ y : ℝ, (cstar W).toReal < y →
        X.GeneratorIntegrable (vcstar W) y ∧
          X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 < x →
        valueFunction X q x = ENNReal.ofReal (vcstar W x)) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ y : ℝ, (cstar W).toReal < y →
          X.GeneratorIntegrable (vcstar W) y ∧
            X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by
  have hc : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hzero :=
    avram_sweep16_original_ubv_complete_root_at_zero X hX hBV q hq W hW
  refine ⟨hc, ?_, ?_⟩
  · intro x hx
    by_cases hxp : 0 < x
    · obtain ⟨hAdmissible, hDividend⟩ :=
        barrier_cstar_attains_value_all_capital X hX q hq W hW hc x hx
      exact ⟨hAdmissible, hDividend, hCapPositive x hxp⟩
    · have hxzero : x = 0 := le_antisymm (le_of_not_gt hxp) hx
      subst x
      exact ⟨hzero.1, hzero.2.1, hzero.2.2.1⟩
  · intro hgen x hx
    by_cases hxp : 0 < x
    · obtain ⟨hAdmissible, _hDividend⟩ :=
        barrier_cstar_attains_value_all_capital X hX q hq W hW hc x hx
      exact ⟨hAdmissible.1, hTopPositive hgen x hxp⟩
    · have hxzero : x = 0 := le_antisymm (le_of_not_gt hxp) hx
      subst x
      exact ⟨hzero.2.2.2.1, hzero.2.2.2.2⟩
