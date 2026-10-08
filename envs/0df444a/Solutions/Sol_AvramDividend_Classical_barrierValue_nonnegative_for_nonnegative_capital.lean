-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_nonnegative_for_nonnegative_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:01:30.435997+00:00
-- url     : https://prove2.me/submissions/63d0d074-883e-4dbc-8613-00bdb298c819

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_at_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    0 ≤ barrierValue W a x := by
  have hnotx : ¬ x < 0 := not_lt.mpr hx
  by_cases hxa : x ≤ a
  · by_cases ha0 : a = 0
    · have hx0 : x = 0 := le_antisymm (by simpa [ha0] using hxa) hx
      subst x
      subst a
      exact AvramDividend.Classical.barrierValue_zero_boundary_nonneg X hX q hq W hW
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hWx : 0 ≤ W x := hW.2.1 x hx
      have hmono : MonotoneOn W (Ici 0) := hW.2.2.2.1
      let g : ℝ → ℝ := fun z => W (max z 0)
      have hgmono : Monotone g := by
        intro s t hst
        apply hmono
        · exact le_max_right s 0
        · exact le_max_right t 0
        · exact max_le_max hst le_rfl
      have he : W =ᶠ[𝓝 a] g := by
        filter_upwards [Ioi_mem_nhds hap] with z hz
        simp only [g, max_eq_left (le_of_lt (Set.mem_Ioi.mp hz))]
      have hderiv : 0 ≤ deriv W a := by
        rw [Filter.EventuallyEq.deriv_eq he]
        exact hgmono.deriv_nonneg
      have hformula : barrierValue W a x = W x / deriv W a := by
        simp [barrierValue, hnotx, hxa, scaleDeriv, ha0, divE]
      rw [hformula]
      exact div_nonneg hWx hderiv
  · have hax : a < x := lt_of_not_ge hxa
    have hgap : 0 ≤ x - a := sub_nonneg.mpr (le_of_lt hax)
    have hboundary : 0 ≤ barrierValue W a a :=
      AvramDividend.Classical.barrierValue_nonnegative_at_nonnegative_barrier
        X hX q hq W hW a ha
    have hnot_a : ¬ a < 0 := not_lt.mpr ha
    have hformula :
        barrierValue W a x = (x - a) + barrierValue W a a := by
      simp [barrierValue, hnotx, hxa, hnot_a]
    rw [hformula]
    exact add_nonneg hgap hboundary
