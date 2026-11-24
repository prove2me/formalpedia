-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.residues_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:33.798799+00:00
-- url     : https://prove2.me/submissions/e8eef745-afa8-4e28-b378-31cbc69e42de

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe
import Theorems.Thm_Formalism_GaloisIrreducibility_card_pow_eq_one_le_two_mul
import Theorems.Thm_Formalism_GaloisIrreducibility_card_residues_le_units
import Theorems.Thm_Formalism_GaloisIrreducibility_index_zpowers_five

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : ResiduesLe := by
  classical
  intro l j D hl hD
  have hD0 : 0 < D := hD
  have : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.ne_zero⟩
  refine (card_residues_le_units (l ^ j) D hD0).trans ?_
  by_cases hcyc : IsCyclic (ZMod (l ^ j))ˣ
  · exact card_pow_eq_one_le_two_mul (⊤ : Subgroup (ZMod (l ^ j))ˣ)
      (by rw [Subgroup.index_top]; norm_num) hD0
  · have hl2 : l = 2 := by
      by_contra hne
      exact hcyc (ZMod.isCyclic_units_of_prime_pow l hl hne j)
    subst hl2
    have hj : ¬ j ≤ 2 := fun hj => hcyc ((ZMod.isCyclic_units_two_pow_iff j).2 hj)
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
    have h5 : Nat.Coprime 5 (2 ^ (n + 2)) :=
      Nat.Coprime.pow_right _ (by norm_num)
    exact card_pow_eq_one_le_two_mul (Subgroup.zpowers (ZMod.unitOfCoprime 5 h5))
      (by rw [index_zpowers_five n h5]) hD0
end Formalism.GaloisIrreducibility
