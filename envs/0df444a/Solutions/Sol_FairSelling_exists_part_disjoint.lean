-- Prove2me | solution 1 for FairSelling.exists_part_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:03:28.615693+00:00
-- url     : https://prove2.me/submissions/7acd566b-359c-473e-9b9c-eef30611bdd3

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (A : Fin 3 → Finset G)
    (hA : ∀ i j : Fin 3, i ≠ j → Disjoint (A i) (A j))
    (X : Finset G) (hX : X.card ≤ 2) : ∃ j : Fin 3, Disjoint (A j) X := by
  classical
  by_contra hcon
  push_neg at hcon
  choose g hg1 hg2 using fun j => Finset.not_disjoint_iff.mp (hcon j)
  have hinj : Set.InjOn g (Finset.univ : Finset (Fin 3)) := by
    intro i _ j _ hij
    by_contra hne
    exact (Finset.disjoint_left.mp (hA i j hne)) (hg1 i) (hij ▸ hg1 j)
  have hcard : (Finset.univ : Finset (Fin 3)).card ≤ X.card :=
    Finset.card_le_card_of_injOn g (fun j _ => hg2 j) hinj
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega
end FairSelling
