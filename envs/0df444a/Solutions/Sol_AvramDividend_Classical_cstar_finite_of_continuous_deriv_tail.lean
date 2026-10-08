-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_of_continuous_deriv_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T15:44:43.937288+00:00
-- url     : https://prove2.me/submissions/66b158f5-2c85-4121-b021-3a76ea2f8142

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_iff_minimizer_or_zero_boundary

open AvramDividend.Classical Filter Set
open scoped ENNReal

theorem solution (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (hboundary : derivZeroPlus W ≤ ((deriv W 0 : ℝ) : EReal))
    (htail : ∀ᶠ x : ℝ in
      Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici (0 : ℝ)),
      deriv W 0 ≤ deriv W x) :
    cstar W < ⊤ := by
  have h0mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
  obtain ⟨a, ha, hmin⟩ :=
    hcont.exists_isMinOn' isClosed_Ici h0mem htail
  apply (cstar_lt_top_iff_minimizer_or_zero_boundary W).2
  by_cases hapos : 0 < a
  · left
    exact ⟨a, hapos, fun x hx =>
      hmin (Set.mem_Ici.mpr hx.le)⟩
  · right
    have ha0 : (0 : ℝ) ≤ a := Set.mem_Ici.mp ha
    have haeq : a = 0 := le_antisymm (le_of_not_gt hapos) ha0
    intro x hx
    have hmin0 : deriv W 0 ≤ deriv W x := by
      have hmemb := hmin (Set.mem_Ici.mpr hx.le)
      change deriv W a ≤ deriv W x at hmemb
      simpa only [haeq] using hmemb
    have hcoe :
        ((deriv W 0 : ℝ) : EReal) ≤ ((deriv W x : ℝ) : EReal) := by
      exact_mod_cast hmin0
    exact hboundary.trans hcoe
