-- Prove2me | solution 1 for Formalism.CyclotomicNorms.SubstitutionExponents.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:51.581797+00:00
-- url     : https://prove2.me/submissions/4fd180ed-7e2b-4d70-b6f0-03f7a7651e09

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.SubstitutionExponents
variable {r : ℕ}
namespace Formalism.CyclotomicNorms.SubstitutionExponents
theorem _root_.solution (g : Fin r → ℕ) (j : Fin r) :
    ∑ i, g i = ∑ i ∈ univ.filter (· < j), g i + g j + ∑ i ∈ univ.filter (j < ·), g i := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (· < j)]
  have h : univ.filter (fun i => ¬ i < j) = insert j (univ.filter (j < ·)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, not_lt]
    exact le_iff_eq_or_lt.trans (or_congr eq_comm Iff.rfl)
  rw [h, Finset.sum_insert (by simp), add_assoc]
end Formalism.CyclotomicNorms.SubstitutionExponents
