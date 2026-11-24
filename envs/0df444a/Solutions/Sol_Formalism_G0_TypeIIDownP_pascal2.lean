-- Prove2me | solution 1 for Formalism.G0.TypeIIDownP.pascal2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:26.604869+00:00
-- url     : https://prove2.me/submissions/686b3ff1-08e8-4ece-982e-67fcbe1ab967

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIDown
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_eq_zero
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_succ_succ
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_zero_right
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_zero_succ
import Theorems.Thm_Formalism_G0_SubspaceCountP_gb_eq_zero
import Theorems.Thm_Formalism_G0_SubspaceCountP_gb_succ_succ
import Theorems.Thm_Formalism_G0_SubspaceCountP_gb_zero_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TypeIIDownP
open QVandermondeP
namespace Formalism.G0.TypeIIDownP
theorem _root_.solution (q M n : ℕ) :
    gaussBinom q (M + 1) (n + 1) = gaussBinom q M (n + 1) + q ^ (M - n) * gaussBinom q M n := by
  induction M generalizing n with
  | zero =>
    cases n with
    | zero =>
      rw [Formalism.G0.QVandermondeP.gb_succ_succ q 0 0,
        Formalism.G0.QVandermondeP.gb_zero_succ q 0,
        Formalism.G0.QVandermondeP.gb_zero_right q 0]
      simp
    | succ k =>
      rw [Formalism.G0.QVandermondeP.gb_eq_zero q (0 + 1) (k + 1 + 1) (by omega),
        Formalism.G0.QVandermondeP.gb_zero_succ q (k + 1),
        Formalism.G0.QVandermondeP.gb_zero_succ q k]
      simp
  | succ M ih =>
    cases n with
    | zero =>
      have s1 := Formalism.G0.QVandermondeP.gb_succ_succ q (M + 1) 0
      have s3 := Formalism.G0.QVandermondeP.gb_succ_succ q M 0
      have d1 := ih 0
      have z1 := Formalism.G0.QVandermondeP.gb_zero_right q (M + 1)
      have z0 := Formalism.G0.QVandermondeP.gb_zero_right q M
      calc gaussBinom q (M + 1 + 1) (0 + 1)
          = 1 + q ^ (0 + 1) * gaussBinom q (M + 1) (0 + 1) := by rw [s1, z1]
        _ = 1 + q ^ (0 + 1) * (gaussBinom q M (0 + 1) + q ^ (M - 0) * gaussBinom q M 0) := by
          rw [d1]
        _ = (gaussBinom q M 0 + q ^ (0 + 1) * gaussBinom q M (0 + 1)) + q ^ (M + 1 - 0) * 1 := by
          rw [z0, Nat.sub_zero, Nat.sub_zero]; ring
        _ = gaussBinom q (M + 1) (0 + 1) + q ^ (M + 1 - 0) * gaussBinom q (M + 1) 0 := by
          rw [s3, z1]
    | succ k =>
      have s1 := Formalism.G0.QVandermondeP.gb_succ_succ q (M + 1) (k + 1)
      have s2 := Formalism.G0.QVandermondeP.gb_succ_succ q M (k + 1)
      have s3 := Formalism.G0.QVandermondeP.gb_succ_succ q M k
      have d1 := ih k
      have d2 := ih (k + 1)
      have e : q ^ (k + 1 + 1) * (q ^ (M - (k + 1)) * gaussBinom q M (k + 1)) =
          q ^ (M - k) * (q ^ (k + 1) * gaussBinom q M (k + 1)) := by
        by_cases h : k + 1 ≤ M
        · rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
          have hx : k + 1 + 1 + (M - (k + 1)) = M - k + (k + 1) := by omega
          rw [hx]
        · simp [Formalism.G0.QVandermondeP.gb_eq_zero q M (k + 1) (by omega)]
      rw [Nat.add_sub_add_right]
      calc gaussBinom q (M + 1 + 1) (k + 1 + 1)
          = gaussBinom q (M + 1) (k + 1) + q ^ (k + 1 + 1) * gaussBinom q (M + 1) (k + 1 + 1) := s1
        _ = (gaussBinom q M (k + 1) + q ^ (M - k) * gaussBinom q M k) +
              q ^ (k + 1 + 1) * (gaussBinom q M (k + 1 + 1) +
                q ^ (M - (k + 1)) * gaussBinom q M (k + 1)) := by rw [d1, d2]
        _ = gaussBinom q M (k + 1) + q ^ (M - k) * gaussBinom q M k +
              q ^ (k + 1 + 1) * gaussBinom q M (k + 1 + 1) +
              q ^ (k + 1 + 1) * (q ^ (M - (k + 1)) * gaussBinom q M (k + 1)) := by ring
        _ = gaussBinom q M (k + 1) + q ^ (M - k) * gaussBinom q M k +
              q ^ (k + 1 + 1) * gaussBinom q M (k + 1 + 1) +
              q ^ (M - k) * (q ^ (k + 1) * gaussBinom q M (k + 1)) := by rw [e]
        _ = (gaussBinom q M (k + 1) + q ^ (k + 1 + 1) * gaussBinom q M (k + 1 + 1)) +
              q ^ (M - k) * (gaussBinom q M k + q ^ (k + 1) * gaussBinom q M (k + 1)) := by ring
        _ = gaussBinom q (M + 1) (k + 1 + 1) + q ^ (M - k) * gaussBinom q (M + 1) (k + 1) := by
          rw [s2, s3]
end Formalism.G0.TypeIIDownP
