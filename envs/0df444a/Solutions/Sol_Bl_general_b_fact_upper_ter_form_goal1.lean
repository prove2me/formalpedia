-- Prove2me | solution 1 for Bl.general_b_fact_upper_ter_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:12.29393+00:00
-- url     : https://prove2.me/submissions/9eb64ade-6bff-4f76-93fe-b96344177da4

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.general_b_fact_upper_ter_form
private lemma aux {p : Nat} [Fact (Nat.Prime p)] {ι : Type} (s : Finset ι) (g : ι → PadicAlgCl p) {C : Real}
    (hC : 0 ≤ C) (h : ∀ j ∈ s, ‖g j‖ ≤ C) : ‖∑ j ∈ s, g j‖ ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h a (Finset.mem_insert_self a t)
    · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
end Bl.general_b_fact_upper_ter_form
end

set_option autoImplicit false
open Bl Bl.general_b_fact_upper_ter_form
namespace Bl.general_b_fact_upper_ter_form
theorem _root_.solution :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset.{0} ι) (g : ι → PadicAlgCl p) {C : Real},
  LE.le.{0} 0 C →
    (∀ (j : ι), Membership.mem.{0, 0} s j → LE.le.{0} (Norm.norm.{0} (g j)) C) →
      LE.le.{0} (Norm.norm.{0} (Finset.sum.{0, 0} s fun (j : ι) ↦ g j)) C := by
  intro p _ ι s g C hC h
  exact aux s g hC h
end Bl.general_b_fact_upper_ter_form
