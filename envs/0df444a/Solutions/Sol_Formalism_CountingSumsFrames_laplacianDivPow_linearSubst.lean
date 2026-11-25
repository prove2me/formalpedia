-- Prove2me | solution 1 for Formalism.CountingSumsFrames.laplacianDivPow_linearSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:59:46.158319+00:00
-- url     : https://prove2.me/submissions/dee11ee3-8cf8-4e9f-96d0-8ecd200349e9

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_laplacian_pow_linearSubst

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
    ctrDiv K k l (glAct g f) = glAct g (ctrDiv K k l f) := by
  simp only [ctrDiv, LinearMap.smul_apply, map_smul, laplacian_pow_linearSubst]
end Formalism.CountingSumsFrames
