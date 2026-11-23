-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.finite_polAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:58.315447+00:00
-- url     : https://prove2.me/submissions/4d975307-63c1-434e-a924-c5f02ed1133e

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_finrank_polAB

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
open Har2
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution (k' A B : ℕ) : Module.Finite K (PolAB K (k' + 1) A B) := by
  exact Module.finite_of_finrank_pos (by
    rw [finrank_polAB]
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
end Formalism.CountingSumsFrames.Har2
