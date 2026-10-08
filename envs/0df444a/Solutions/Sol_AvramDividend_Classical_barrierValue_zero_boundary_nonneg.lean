-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_zero_boundary_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:43:46.536675+00:00
-- url     : https://prove2.me/submissions/5f6dc89f-845b-4144-99ce-0cb28fccbc80

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
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 := by
  have hW0 : 0 ≤ W 0 := hW.2.1 0 le_rfl
  have hmono : MonotoneOn W (Ici 0) := hW.2.2.2.1
  let g : ℝ → ℝ := fun z => W (max z 0)
  have hgmono : Monotone g := by
    intro s t hst
    apply hmono
    · exact le_max_right s 0
    · exact le_max_right t 0
    · exact max_le_max hst le_rfl
  have hderiv (y : ℝ) (hy : 0 < y) : 0 ≤ deriv W y := by
    have he : W =ᶠ[𝓝 y] g := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      simp only [g, max_eq_left (le_of_lt (Set.mem_Ioi.mp hz))]
    rw [Filter.EventuallyEq.deriv_eq he]
    exact hgmono.deriv_nonneg
  have hlim : (0 : EReal) ≤ derivZeroPlus W := by
    unfold derivZeroPlus
    have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ),
        (0 : EReal) ≤ ((deriv W y : ℝ) : EReal) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact_mod_cast hderiv y (Set.mem_Ioi.mp hy)
    exact Filter.le_liminf_of_le (h := hev)
  have heq : barrierValue W 0 0 = divE (W 0) (derivZeroPlus W) := by
    simp [barrierValue, scaleDeriv]
  rw [heq]
  unfold divE
  split_ifs with hinfty
  · positivity
  · exact div_nonneg hW0 (EReal.toReal_nonneg hlim)
