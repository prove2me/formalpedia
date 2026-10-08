-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_deriv_nonneg_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:56:42.828501+00:00
-- url     : https://prove2.me/submissions/198cec6b-26a5-4d28-b4d6-cec51ea8360f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    0 ≤ deriv W a := by
  have hmono : MonotoneOn W (Ici 0) := hW.2.2.2.1
  let g : ℝ → ℝ := fun z => W (max z 0)
  have hgmono : Monotone g := by
    intro s t hst
    apply hmono
    · exact le_max_right s 0
    · exact le_max_right t 0
    · exact max_le_max hst le_rfl
  have he : W =ᶠ[𝓝 a] g := by
    filter_upwards [Ioi_mem_nhds ha] with z hz
    simp only [g, max_eq_left (le_of_lt (Set.mem_Ioi.mp hz))]
  rw [Filter.EventuallyEq.deriv_eq he]
  exact hgmono.deriv_nonneg
