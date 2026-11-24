-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.wt_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:51:00.983099+00:00
-- url     : https://prove2.me/submissions/45ffe791-a23b-4224-9f12-083ce4249ef6

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL L2 : Letters N) (j : ℕ) (c : Fin r) {m m' : Fin N × Fin r →₀ ℕ}
    (hm : MultiDeg L2 m) (hm' : MultiDeg L2 m') : wt LL j c m' - wt LL j c m ≤ (L2.total : ℤ) := by
  unfold wt Letters.total
  rw [← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : m (i, c) ≤ L2.deg i := by
    rw [← hm i]
    exact Finset.single_le_sum (f := fun c => m (i, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have h2 : m' (i, c) ≤ L2.deg i := by
    rw [← hm' i]
    exact Finset.single_le_sum (f := fun c => m' (i, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  split_ifs <;> omega
end Formalism.InvariantFactorPaths.PW
