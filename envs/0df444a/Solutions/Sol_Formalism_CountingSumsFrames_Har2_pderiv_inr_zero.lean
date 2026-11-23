-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.pderiv_inr_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:01.337255+00:00
-- url     : https://prove2.me/submissions/12dcba05-a204-4258-8f33-414452954f53

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
private theorem apply_inr_le_yDeg (m : XY k →₀ ℕ) (i : Fin k) : m (Sum.inr i) ≤ yDeg m := by
  unfold yDeg
  exact Finset.single_le_sum (f := fun j => m (Sum.inr j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
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
theorem _root_.solution {A : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k A 0) :
    pderiv (Sum.inr i) f = 0 := by
  have key := lin_eq (A := A) (B := 0) (pderiv (R := K) (Sum.inr i : XY k)).toLinearMap 0
    (fun m c _ hy => by
      have h0 : m (Sum.inr i) = 0 := by have := apply_inr_le_yDeg m i; omega
      change pderiv (Sum.inr i) (monomial m c) = (0 : PolXY K k →ₗ[K] PolXY K k) (monomial m c)
      rw [LinearMap.zero_apply, pderiv_monomial, h0, Nat.cast_zero, mul_zero, monomial_zero]) hf
  simpa using key
end Formalism.CountingSumsFrames.Har2
