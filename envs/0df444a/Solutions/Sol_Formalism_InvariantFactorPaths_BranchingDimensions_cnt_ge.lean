-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.cnt_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:43:46.309939+00:00
-- url     : https://prove2.me/submissions/90e9649c-874d-4f59-abfd-aa48dfa4e8af

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementL
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LDigits
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_cnt_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_cnt_two

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (T Q : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) (s : ℕ) :
    ∀ c, T ^ s * (T - (Q - T)) ≤ cnt T Q (s + 2) c := by
  induction s with
  | zero =>
    intro c
    rw [pow_zero, one_mul]
    exact cnt_two T Q c hQ hT
  | succ s ih =>
    intro c
    rw [show s + 1 + 2 = (s + 2) + 1 by omega, cnt_succ T Q (s + 2) c hQ]
    calc T ^ (s + 1) * (T - (Q - T)) = ∑ _a : Fin T, T ^ s * (T - (Q - T)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
      _ ≤ ∑ a : Fin T, cnt T Q (s + 2) (c + (Q - 1) * a) :=
          Finset.sum_le_sum (fun a _ => ih _)
end Formalism.InvariantFactorPaths.BranchingDimensions
