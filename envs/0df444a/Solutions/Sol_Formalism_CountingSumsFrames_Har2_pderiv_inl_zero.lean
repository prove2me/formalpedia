-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.pderiv_inl_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:48.126205+00:00
-- url     : https://prove2.me/submissions/e472b557-a6bb-4f17-84c6-e695a2265312

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_lin_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
private theorem apply_inl_le_xDeg (m : XY k →₀ ℕ) (i : Fin k) : m (Sum.inl i) ≤ xDeg m := by
  unfold xDeg
  exact Finset.single_le_sum (f := fun j => m (Sum.inl j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
end Har2
open Har2
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
end Har2
end Formalism.CountingSumsFrames
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution {B : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k 0 B) :
    pderiv (Sum.inl i) f = 0 := by
  have key := lin_eq (A := 0) (B := B) (pderiv (R := K) (Sum.inl i : XY k)).toLinearMap 0
    (fun m c hx _ => by
      have h0 : m (Sum.inl i) = 0 := by have := apply_inl_le_xDeg m i; omega
      change pderiv (Sum.inl i) (monomial m c) = (0 : PolXY K k →ₗ[K] PolXY K k) (monomial m c)
      rw [LinearMap.zero_apply, pderiv_monomial, h0, Nat.cast_zero, mul_zero, monomial_zero]) hf
  simpa using key
end Formalism.CountingSumsFrames.Har2
