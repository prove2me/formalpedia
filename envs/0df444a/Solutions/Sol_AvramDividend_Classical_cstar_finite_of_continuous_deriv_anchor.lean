-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_of_continuous_deriv_anchor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:40:29.944841+00:00
-- url     : https://prove2.me/submissions/bcdbff92-3836-40ad-97a0-b576864cb4f6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_iff_minimizer_or_zero_boundary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set
open scoped ENNReal

theorem solution (W : ℝ → ℝ) (b : ℝ)
    (hb : 0 ≤ b)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (hboundary : derivZeroPlus W ≤ ((deriv W 0 : ℝ) : EReal))
    (htail : ∀ᶠ x : ℝ in
      Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici (0 : ℝ)),
      deriv W b ≤ deriv W x) :
    cstar W < ⊤ := by
  have hbmem : b ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hb
  obtain ⟨a, ha, hmin⟩ :=
    hcont.exists_isMinOn' isClosed_Ici hbmem htail
  apply (cstar_lt_top_iff_minimizer_or_zero_boundary W).2
  by_cases hapos : 0 < a
  · left
    exact ⟨a, hapos, fun x hx =>
      hmin (Set.mem_Ici.mpr hx.le)⟩
  · right
    have ha0 : (0 : ℝ) ≤ a := Set.mem_Ici.mp ha
    have haeq : a = 0 := le_antisymm (le_of_not_gt hapos) ha0
    intro x hx
    have hminx := hmin (Set.mem_Ici.mpr hx.le)
    change deriv W a ≤ deriv W x at hminx
    have hmin0 : deriv W 0 ≤ deriv W x := by
      simpa only [haeq] using hminx
    have hcoe :
        ((deriv W 0 : ℝ) : EReal) ≤ ((deriv W x : ℝ) : EReal) := by
      exact_mod_cast hmin0
    exact hboundary.trans hcoe
