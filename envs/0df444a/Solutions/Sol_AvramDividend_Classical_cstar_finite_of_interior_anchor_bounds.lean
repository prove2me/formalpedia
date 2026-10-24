-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_of_interior_anchor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:24:04.1482+00:00
-- url     : https://prove2.me/submissions/62769e2c-e5fd-46d9-a2fa-1ee91a0fdc7d

import Mathlib.Topology.Order.Compact
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_minimizer

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set
open scoped ENNReal

/-- A derivative minimum above an interior anchor remains minimal below
    the anchor under the stated comparison hypothesis. -/
theorem solution (W : ℝ → ℝ) (a : ℝ)
    (ha : 0 < a)
    (hcont : ContinuousOn (deriv W) (Set.Ici a))
    (hnear : ∀ x : ℝ, 0 < x → x ≤ a → deriv W a ≤ deriv W x)
    (htail : ∀ᶠ x : ℝ in
      Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici a),
      deriv W a ≤ deriv W x) :
    cstar W < ⊤ := by
  have haMem : a ∈ Set.Ici a := Set.mem_Ici.mpr le_rfl
  obtain ⟨b, hb, hmin⟩ :=
    hcont.exists_isMinOn' isClosed_Ici haMem htail
  have hbpos : 0 < b := lt_of_lt_of_le ha (Set.mem_Ici.mp hb)
  have hba : deriv W b ≤ deriv W a := hmin haMem
  have hglobal : ∀ x : ℝ, 0 < x → deriv W b ≤ deriv W x := by
    intro x hx
    by_cases hxa : x ≤ a
    · exact hba.trans (hnear x hx hxa)
    · exact hmin (Set.mem_Ici.mpr (le_of_lt (lt_of_not_ge hxa)))
  exact cstar_lt_top_of_minimizer W ⟨b, hbpos, hglobal⟩
