-- Prove2me | solution 1 for Formalism.CountingSumsFrames.laplacian_pow_linearSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:12.690439+00:00
-- url     : https://prove2.me/submissions/d1070c82-54fc-442e-b73e-cc903b8954e0

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_laplacian_linearSubst

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
theorem _root_.solution (g : GL (Fin k) K) (l : ℕ) : ∀ f : PolXY K k,
    (ctrF K k ^ l) (glAct g f) = glAct g ((ctrF K k ^ l) f) := by
  induction l with
  | zero => intro f; simp
  | succ l ih => intro f; rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, laplacian_linearSubst, ih]
end Formalism.CountingSumsFrames
