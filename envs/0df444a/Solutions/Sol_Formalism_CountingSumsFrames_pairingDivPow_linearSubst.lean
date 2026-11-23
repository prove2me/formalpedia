-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pairingDivPow_linearSubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:25.592643+00:00
-- url     : https://prove2.me/submissions/052e6446-3a87-4ebf-9b78-2427ba1dbede

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_linearSubst_pairing

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
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (g : GL (Fin k) K) (l : ℕ) (f : PolXY K k) :
    hDiv K k l (glAct g f) = glAct g (hDiv K k l f) := by
  simp only [hDiv, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul, map_mul, map_pow, linearSubst_pairing]
end Formalism.CountingSumsFrames
