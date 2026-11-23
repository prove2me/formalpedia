-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.h_pow_mul_mem_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:45.070798+00:00
-- url     : https://prove2.me/submissions/88e4b87c-666d-43ba-b2d7-36b6a3f98ca5

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_h_mul_mem_gauss

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
theorem _root_.solution {K : Type} [Field K] {k : ℕ} (R : Subring K) (j : ℕ) (G : PolXY K k)
    (hG : G ∈ GaussLat R) : hXY K k ^ j * G ∈ GaussLat R := by
  induction j with
  | zero => simpa using hG
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    exact h_mul_mem_gauss R _ ih
end Formalism.CountingSumsFrames.Har4
