-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_sum_wtT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:50.427488+00:00
-- url     : https://prove2.me/submissions/5c77b4b1-b001-4807-b0f5-145763b25c37

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (I : TIdx mu) (s : Finset (Fin n)) :
    ∑ b ∈ s, qb_wtT mu I b =
      (s.card : ℤ) * mu (lastIdx n) + ∑ c : ↥(TCols mu), ((s.filter (· ∈ (I c).1)).card : ℤ) := by
  unfold qb_wtT
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  congr 1
  simp only [card_filter, Nat.cast_sum]
  rw [sum_comm]
end Formalism.InvariantFactorPaths.ColumnFamilies
