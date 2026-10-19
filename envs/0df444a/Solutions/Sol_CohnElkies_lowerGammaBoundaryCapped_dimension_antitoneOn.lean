-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryCapped_dimension_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/89304203-586c-4615-a725-7e42aa1b10df

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_antitoneOn

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (R D : ℝ) :
    AntitoneOn
      (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D)
      (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  by_cases hxzero : x = 0
  · subst x
    unfold lowerGammaBoundaryCapped
    simp only [ite_true]
    split_ifs with hyzero
    · exact le_rfl
    · exact min_le_right _ _
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
    have hgamma := lowerGammaBoundaryLog_dimension_antitoneOn
      (d := d) R (show x ∈ Ioi (0 : ℝ) from hxpos)
        (show y ∈ Ioi (0 : ℝ) from hypos) hxy
    simp only [lowerGammaBoundaryCapped,
      if_neg hxpos.ne', if_neg hypos.ne']
    exact min_le_min hgamma (le_refl D)
end CohnElkies
