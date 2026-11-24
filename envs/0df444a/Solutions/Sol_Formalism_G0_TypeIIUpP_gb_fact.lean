-- Prove2me | solution 1 for Formalism.G0.TypeIIUpP.gb_fact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:46.410798+00:00
-- url     : https://prove2.me/submissions/50ea9d58-3504-4517-819b-3815a9dad91d

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp
import Theorems.Thm_Formalism_G0_TypeIIUpP_qfact_succ
import Theorems.Thm_Formalism_G0_TypeIIUpP_qint_add
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_eq_zero
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_succ_succ
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_zero_right
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
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.TypeIIUpP
namespace Formalism.G0.TypeIIUpP
theorem _root_.solution (q : ℕ) : ∀ n k : ℕ, k ≤ n →
    gaussBinom q n k * qfact q k * qfact q (n - k) = qfact q n
  | 0, 0, _ => by simp [gaussBinom, qfact]
  | n + 1, 0, _ => by simp [QVandermondeP.gb_zero_right, qfact]
  | 0, k + 1, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [QVandermondeP.gb_succ_succ]
    have e1 : n + 1 - (k + 1) = n - k := by omega
    rw [e1, qfact_succ q k, qfact_succ q n]
    have h1 := solution q n k (by omega)
    rcases Nat.lt_or_ge k n with hk | hk
    · have h2 := solution q n (k + 1) (by omega)
      have e2 : n - k = (n - (k + 1)) + 1 := by omega
      have e3 : n + 1 = (k + 1) + (n - k) := by omega
      have key : qint q (n + 1) = qint q (k + 1) + q ^ (k + 1) * qint q (n - k) := by
        rw [e3, qint_add]
      rw [key]
      have hq : qfact q (n - k) = qfact q (n - (k + 1)) * qint q (n - k) := by
        conv_lhs => rw [e2]
        rw [qfact_succ]
        rw [← e2]
      calc (gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1)) * (qfact q k * qint q (k + 1)) *
            qfact q (n - k)
          = (gaussBinom q n k * qfact q k * qfact q (n - k)) * qint q (k + 1)
            + q ^ (k + 1) * (gaussBinom q n (k + 1) * (qfact q k * qint q (k + 1)) *
              qfact q (n - (k + 1))) * qint q (n - k) := by rw [hq]; ring
        _ = qfact q n * (qint q (k + 1) + q ^ (k + 1) * qint q (n - k)) := by
          rw [h1, ← qfact_succ, h2]; ring
    · have hkn : k = n := by omega
      subst hkn
      rw [QVandermondeP.gb_eq_zero q k (k + 1) (by omega)]
      have : (gaussBinom q k k + q ^ (k + 1) * 0) * (qfact q k * qint q (k + 1)) * qfact q (k - k)
          = (gaussBinom q k k * qfact q k * qfact q (k - k)) * qint q (k + 1) := by ring
      rw [this, h1]
end Formalism.G0.TypeIIUpP
