-- Prove2me | solution 1 for FairSelling.fin3_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:26.652513+00:00
-- url     : https://prove2.me/submissions/6f233cfb-36c8-444c-9880-bf8cb12670e7

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_fin3_cover
attribute [local simp] FairSelling.restrictVal_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution {M : Type*} [AddCommMonoid M] {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Fin 3 → M) :
    ∑ i, f i = f a + f b + f c := by
  have h3 : ({a, b, c} : Finset (Fin 3)) = Finset.univ := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
    exact fin3_cover hab hac hbc x
  rw [← h3, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, add_assoc]
end FairSelling
