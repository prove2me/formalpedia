-- Prove2me | solution 1 for Eden.eventually_dimension_formula_two_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:56.88485+00:00
-- url     : https://prove2.me/submissions/1bd15521-bc83-4bd6-b85e-5541b45c3f05

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
import Theorems.Thm_Eden_normalized_first_two_nonneg_of_radii
import Theorems.Thm_Eden_eventually_dimension_formula_of_neutral_prefix
import Theorems.Thm_Eden_descending_radiusPairSpectrum_two_two
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum
import Theorems.Thm_Eden_one_lt_of_limitingSquaredRadius_eq_two


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 2)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 2) :
    ∀ᶠ t in atTop,
      (∀ i : Fin 5, i.val < 2 → 0 ≤ normalizedLogSingularValues c t p i) ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 3 < 0 ∧
      normalizedLogSingularValues c t p 2 < 0 ∧
      finiteTimeDimension c t p = 2 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 2 /
          -normalizedLogSingularValues c t p 2 := by
  have ha := lyapunovExponent_eq_radiusPairSpectrum c p
  rw [h₁, h₂, descending_radiusPairSpectrum_two_two hc] at ha
  apply eventually_dimension_formula_of_neutral_prefix c p (k := 2) (by omega)
  · intro i hi
    rw [ha]
    fin_cases i <;> norm_num at *
  · rw [ha]; norm_num
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht i hi
    exact normalized_first_two_nonneg_of_radii c ht hp
      (one_lt_of_limitingSquaredRadius_eq_two h₁).le
      (one_lt_of_limitingSquaredRadius_eq_two h₂).le i hi
end Eden
