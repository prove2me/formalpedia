-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wt_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:37:40.107892+00:00
-- url     : https://prove2.me/submissions/db75ff8d-2285-4219-b727-99df0cdfebcc

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : Fin r)
    (m : Fin (K + 1) × Fin r →₀ ℕ) : wt LL (K + 1) c m = wt LL K c m + (m (Fin.last K, c) : ℤ) := by
  have h1 : ∀ i : Fin K, ((Fin.castSucc i : Fin (K + 1)) : ℕ) < K + 1 := fun i => by
    simp only [Fin.coe_castSucc]
    omega
  have h2 : ∀ i : Fin K, ((Fin.castSucc i : Fin (K + 1)) : ℕ) < K := fun i => by
    simp only [Fin.coe_castSucc]
    exact i.is_lt
  simp only [wt, Fin.sum_univ_castSucc, h1, h2, if_true, Fin.val_last, lt_self_iff_false, if_false,
    Nat.lt_succ_self, hv, add_zero]
end Formalism.InvariantFactorPaths.L4
