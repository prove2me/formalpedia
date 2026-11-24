-- Prove2me | solution 1 for FairSelling.SharedProceeds.sum_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:29.652626+00:00
-- url     : https://prove2.me/submissions/1eb68c13-5e86-44b3-b190-bc3fe0138d6b

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing
import Theorems.Thm_FairSelling_SharedProceeds_sv_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds
namespace FairSelling.SharedProceeds
theorem _root_.solution {A : Finset (Fin 4)} (hA : (0 : Fin 4) ∉ A) : ∑ g ∈ A, sv g ≤ 3 := by
  have hsub : A ⊆ ({1, 2, 3} : Finset (Fin 4)) := by
    intro x hx
    fin_cases x
    · exact absurd hx hA
    all_goals simp
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => sv_nonneg g)) ?_
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [sv, Fin.ext_iff]
end FairSelling.SharedProceeds
