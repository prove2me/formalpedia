-- Prove2me | solution 1 for DeletionCode.CanonicalIndex.flat_rule_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:47.338454+00:00
-- url     : https://prove2.me/submissions/0f925d8e-bb28-4339-84f2-6e3c41e567a9

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex
import Theorems.Thm_DeletionCode_CanonicalIndex_group_sum
import Theorems.Thm_DeletionCode_CanonicalIndex_flat_bubble_spectrum

set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators
namespace DeletionCode.CanonicalIndex
theorem _root_.solution {k : ℕ} (t R : ℕ)
    (words : Fin R → Fin (2 * t) → BubbleWord k) (r : Fin R) :
    ruleSpectrum (flatFamily t R words).family (windowLength k) (groupBubbles (group t R) r) =
      fun g => ∑ j : Fin (2 * t), bubbleSpectrum (pairFamily t R words).family
        (windowLength k) (r, j) g := by
  classical
  funext g
  unfold ruleSpectrum groupBubbles
  rw [group_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrFun (flat_bubble_spectrum t R words ((indexEquiv t R).symm (r, j))) g
  simpa only [Equiv.apply_symm_apply] using h
end DeletionCode.CanonicalIndex
