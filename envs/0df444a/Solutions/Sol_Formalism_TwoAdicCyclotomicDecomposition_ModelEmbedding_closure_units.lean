-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.closure_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:05.439998+00:00
-- url     : https://prove2.me/submissions/f2982180-f2d8-48d7-84a1-32001bec5363

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_card_unitsTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_two_mul_le_of_dvd_ne
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_orderOf_five_units_two_pow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_unitsMap_five_mod_four
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_unitsMap_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open ModelEmbedding
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution (k : ℕ) :
    Subgroup.closure {(-1 : (ZMod (2 ^ (k + 2)))ˣ), u5 (k + 2)} = ⊤ := by
  set H := Subgroup.closure {(-1 : (ZMod (2 ^ (k + 2)))ˣ), u5 (k + 2)} with hH
  have hZ : zpowers (u5 (k + 2)) ≤ H := Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hm : (-1 : (ZMod (2 ^ (k + 2)))ˣ) ∈ H := Subgroup.subset_closure (by simp)
  have h4 : 4 ∣ 2 ^ (k + 2) := ⟨2 ^ k, by ring⟩
  have hnot : (-1 : (ZMod (2 ^ (k + 2)))ˣ) ∉ zpowers (u5 (k + 2)) := by
    intro hmem
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hmem
    have h1 := congrArg (ZMod.unitsMap h4) hj
    rw [map_zpow, unitsMap_five_mod_four, one_zpow, unitsMap_neg_one] at h1
    exact absurd h1 (by decide)
  have hcardZ : Nat.card (zpowers (u5 (k + 2))) = 2 ^ k := by
    rw [Nat.card_zpowers, orderOf_five_units_two_pow]
  have hcardG : Nat.card (ZMod (2 ^ (k + 2)))ˣ = 2 ^ (k + 1) := by
    rw [card_unitsTwoPow (k + 2) (by omega)]
    simp
  have hdvd : Nat.card (zpowers (u5 (k + 2))) ∣ Nat.card H := Subgroup.card_dvd_of_le hZ
  have hne : Nat.card H ≠ Nat.card (zpowers (u5 (k + 2))) := by
    intro heq
    have h2 : zpowers (u5 (k + 2)) = H := Subgroup.eq_of_le_of_card_ge hZ (le_of_eq heq)
    exact hnot (h2 ▸ hm)
  have hle := two_mul_le_of_dvd_ne Nat.card_pos hdvd hne
  apply Subgroup.eq_top_of_card_eq
  refine le_antisymm (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card H)) ?_
  rw [hcardG, pow_succ]
  rw [hcardZ] at hle
  linarith
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
