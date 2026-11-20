-- Prove2me | solution 1 for DeletionCode.ObstructionBound.survival_term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:02:31.517844+00:00
-- url     : https://prove2.me/submissions/d9d6b704-615f-4b9c-bef3-94fd1cc77d3b

import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_ObstructionBound
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionBound
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount
open CircleUniform WitnessCounting ObstructionProbability
open scoped BigOperators ENNReal
namespace DeletionCode.ObstructionBound
theorem _root_.solution (C N Q R : ℕ) (hC : C ≤ N ^ R) (hQ : 8 * N ≤ Q)
    (hQpos : 0 < Q) :
    (C : ENNReal) * ENNReal.ofReal (2 / (Q : ℝ)) ^ R ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ R) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hNQ : 8 * (N : ℝ) ≤ Q := by exact_mod_cast hQ
  have hratio : (N : ℝ) * (2 / (Q : ℝ)) ≤ 1 / 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hQr]
    linarith
  have hcast : (C : ENNReal) ≤ (N : ENNReal) ^ R := by exact_mod_cast hC
  calc
    _ ≤ (N : ENNReal) ^ R * ENNReal.ofReal (2 / (Q : ℝ)) ^ R :=
      mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = ENNReal.ofReal ((N : ℝ) * (2 / (Q : ℝ))) ^ R := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast, mul_pow]
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) ^ R := pow_le_pow_left' (ENNReal.ofReal_le_ofReal hratio) R
    _ = _ := (ENNReal.ofReal_pow (by positivity) R).symm
end DeletionCode.ObstructionBound
