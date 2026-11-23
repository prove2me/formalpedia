-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pairingDivPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:12.798239+00:00
-- url     : https://prove2.me/submissions/42b164c3-ac0f-4e70-bdb6-5ad07d8292d5

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice

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
theorem _root_.solution (l : ℕ) : hDiv K k l = ((l.factorial : K)⁻¹) • (∑ i : Fin k, h3e K i) ^ l := by
  have : (∑ i : Fin k, h3e K i) = LinearMap.mulLeft K (hXY K k) := by
    refine LinearMap.ext fun f => ?_
    simp [h3e, hXY, Finset.sum_mul, LinearMap.sum_apply, mul_assoc]
  rw [this, LinearMap.pow_mulLeft, hDiv]
end Formalism.CountingSumsFrames
