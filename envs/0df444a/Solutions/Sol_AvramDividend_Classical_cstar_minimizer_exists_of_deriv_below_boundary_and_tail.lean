-- Prove2me | solution 1 for AvramDividend.Classical.cstar_minimizer_exists_of_deriv_below_boundary_and_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T15:57:35.921493+00:00
-- url     : https://prove2.me/submissions/b9ff32c5-ccfc-4b94-827a-9eea2ac5539b

import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical Filter Set

theorem solution (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (a : ℝ) (ha : 0 < a) (hstrict : deriv W a < deriv W 0)
    (htail : ∀ᶠ x : ℝ in
      Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici (0 : ℝ)),
      deriv W a ≤ deriv W x) :
    (cstarSet W).Nonempty := by
  have haMem : a ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr ha.le
  obtain ⟨b, hb, hmin⟩ :=
    hcont.exists_isMinOn' isClosed_Ici haMem htail
  have hbpos : 0 < b := by
    by_contra hnot
    have hbzero : b = 0 :=
      le_antisymm (le_of_not_gt hnot) (Set.mem_Ici.mp hb)
    have hmin_a : deriv W b ≤ deriv W a := hmin haMem
    rw [hbzero] at hmin_a
    exact (not_le_of_gt hstrict) hmin_a
  refine ⟨b, ?_⟩
  change 0 < b ∧ ∀ x : ℝ, 0 < x → deriv W b ≤ deriv W x
  exact ⟨hbpos, fun x hx => hmin (Set.mem_Ici.mpr hx.le)⟩
