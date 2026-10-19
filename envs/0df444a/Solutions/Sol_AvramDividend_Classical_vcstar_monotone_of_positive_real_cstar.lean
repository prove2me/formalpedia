-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_monotone_of_positive_real_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:54:20.21332+00:00
-- url     : https://prove2.me/submissions/4ab1beb9-0e7b-461b-ac69-4f0bc64d430d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg_of_pos
import Theorems.Thm_AvramDividend_Classical_barrierValue_monotone_of_divE_monotone_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal) :
    Monotone (vcstar W) := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 < a := hpos
  have hd : 0 ≤ deriv W a :=
    scaleFunction_deriv_nonneg_of_pos X q W hW a ha
  have hwmono : Monotone W := scaleFunction_monotone X q W hW
  have hdiv : ∀ z : ℝ,
      divE (W z) (scaleDeriv W a) = W z / deriv W a := by
    intro z
    have ha0 : a ≠ 0 := ne_of_gt ha
    simp [divE, scaleDeriv, ha0]
  have hbranchmono : MonotoneOn
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) (Ici 0) := by
    intro u hu v hv huv
    change divE (W u) (scaleDeriv W a) ≤
      divE (W v) (scaleDeriv W a)
    rw [hdiv u, hdiv v]
    exact div_le_div_of_nonneg_right (hwmono huv) hd
  have hbranchnonneg : ∀ z : ℝ, 0 ≤ z →
      0 ≤ divE (W z) (scaleDeriv W a) := by
    intro z hz
    rw [hdiv z]
    exact div_nonneg (hW.2.1 z hz) hd
  change Monotone (barrierValue W a)
  exact barrierValue_monotone_of_divE_monotone_nonneg W a
    (le_of_lt ha) hbranchmono hbranchnonneg