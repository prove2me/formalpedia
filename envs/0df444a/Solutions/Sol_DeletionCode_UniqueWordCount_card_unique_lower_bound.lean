-- Prove2me | solution 1 for DeletionCode.UniqueWordCount.card_unique_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:54:42.685838+00:00
-- url     : https://prove2.me/submissions/8bfeec51-2a7c-4ff1-aa9a-09910668b3fa

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_OverlapCollision
import Definitions.Def_DeletionCode_FinitePairUnion
import Definitions.Def_DeletionCode_UniqueWordParameters
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_DeletionCode_UniqueWordCount
import Theorems.Thm_DeletionCode_UniqueWordCount_family_partition
import Theorems.Thm_DeletionCode_UniqueWordCount_scaled_nonunique_card_le

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordCount
open Windows HeaderRecovery
attribute [local instance] Classical.propDecidable
namespace DeletionCode.UniqueWordCount
theorem _root_.solution (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ n ≤
      (uniqueWords n k).card := by
  have hpow : (0 : ℚ) < 2 ^ k := pow_pos (by norm_num) _
  have hscaled : ((nonuniqueWords n k).card : ℚ) * (2 : ℚ) ^ k ≤
      (n.choose 2 : ℚ) * (2 : ℚ) ^ n := by
    exact_mod_cast scaled_nonunique_card_le n k hk
  have hbad : ((nonuniqueWords n k).card : ℚ) ≤
      (n.choose 2 : ℚ) / (2 : ℚ) ^ k * (2 : ℚ) ^ n := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hpow).mpr hscaled
  have hpart : ((uniqueWords n k).card : ℚ) + (nonuniqueWords n k).card = (2 : ℚ) ^ n := by
    exact_mod_cast family_partition n k
  nlinarith
end DeletionCode.UniqueWordCount
