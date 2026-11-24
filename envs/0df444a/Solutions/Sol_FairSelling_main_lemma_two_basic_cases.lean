-- Prove2me | solution 1 for FairSelling.main_lemma_two_basic_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:40:37.723544+00:00
-- url     : https://prove2.me/submissions/c961eeaf-5392-4171-9f84-254622409cfc

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_pure_reduction
import Theorems.Thm_FairSelling_untouched_mms_part_reduction
attribute [local simp] FairSelling.restrictVal_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3/4) * MMS 3 w p) (B : Finset G)
    (hcase : vbarSum w p B ≤ (3/4) * MMS 3 w p ∨
      ∃ (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
        (lost j k : Fin 3) (g : G),
        B = {g} ∧ ConfigN 3 w p (MMS 3 w p) A s q ∧
        lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ A lost) :
    (3/4) * MMS 3 w p ≤
      MMS 2 (restrictVal (Finset.univ \ B) w) (restrictVal (Finset.univ \ B) p) := by
  obtain hcase | ⟨A, s, q, lost, j, k, g, hg⟩ := hcase;
  · exact pure_reduction w p hw hp hnobig B hcase;
  · obtain ⟨hB, hcfg, hlj, hlk, hjk, hg⟩ := hg;
    have := untouched_mms_part_reduction w p hw hp A s q hcfg lost j k hlj hlk hjk g hg;
    exact le_trans ( mul_le_of_le_one_left ( MMS_nonneg ( by decide ) _ _ hw hp ) ( by norm_num ) ) ( by simpa only [ hB ] using this )
end FairSelling
