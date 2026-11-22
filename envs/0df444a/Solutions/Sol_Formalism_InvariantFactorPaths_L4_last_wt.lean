-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.last_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:32.540426+00:00
-- url     : https://prove2.me/submissions/0b010b7b-adce-4995-9d31-068a331da5b7

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_single_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c : Fin r) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    wt LL j 0 (Finsupp.single (Fin.last K, c) 1 + m) = wt LL j 0 m + (if c = 0 then 1 else 0) := by
  have hK : K < j := by omega
  rw [wt_single_add]
  simp [Fin.val_last, hK, hv]
end Formalism.InvariantFactorPaths.L4
