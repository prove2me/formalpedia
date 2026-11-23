-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.coeff_mem_of_h_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:36.080048+00:00
-- url     : https://prove2.me/submissions/08ca1630-f235-40ed-9276-e7ec91b6c0f4

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_coeff_mem_of_h_mul

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
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {K : Type} [Field K] {k : ℕ} (R : Subring K) (i0 : Fin k) (j : ℕ)
    (G : PolXY K k) (hG : hXY K k ^ j * G ∈ GaussLat R) : G ∈ GaussLat R := by
  induction j generalizing G with
  | zero => simpa using hG
  | succ n ih =>
    have h1 : hXY K k * G ∈ GaussLat R := ih (hXY K k * G) (by rw [← mul_assoc, ← pow_succ]; exact hG)
    exact coeff_mem_of_h_mul R i0 G h1
end Formalism.CountingSumsFrames.Har4
