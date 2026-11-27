-- Prove2me | solution 1 for C6BipartiteDomination.c6_eq_eight_fifteenths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:18:19.008829+00:00
-- url     : https://prove2.me/submissions/f9252dcd-f604-4cac-a655-982ed747165d

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_finite_graph_density_le_eight_fifteenths
import Theorems.Thm_C6BipartiteDomination_corona_density_mem_C6

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace C6BipartiteDomination
theorem _root_.solution : c6 = (8 : ℝ) / 15 := by
  have hupper : ∀ r ∈ C6DensitySet, r ≤ (8 : ℝ) / 15 := by
    intro r hr
    obtain ⟨H, hH, rfl⟩ := hr
    exact finite_graph_density_le_eight_fifteenths hH
  have hbdd : BddAbove C6DensitySet := ⟨(8 : ℝ) / 15, hupper⟩
  have hne : C6DensitySet.Nonempty := ⟨(8 : ℝ) / 15, corona_density_mem_C6⟩
  apply le_antisymm
  · change sSup C6DensitySet ≤ (8 : ℝ) / 15
    exact csSup_le hne hupper
  · change (8 : ℝ) / 15 ≤ sSup C6DensitySet
    exact le_csSup hbdd corona_density_mem_C6
end C6BipartiteDomination
