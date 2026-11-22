-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.yMul_factorization_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:12.297796+00:00
-- url     : https://prove2.me/submissions/b14d4ccd-a67f-43aa-92a0-274b338dd1c1

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_multinomial_factorization_le

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
theorem _root_.solution {k : ℕ} (p : ℕ) (m : XY k →₀ ℕ) :
    (yMul m).factorization p ≤ (k - 1) * Nat.log p (yDeg m) := by
  simpa [yMul, yDeg, Finset.card_univ, Fintype.card_fin] using
    multinomial_factorization_le p Finset.univ (fun i : Fin k => m (Sum.inr i))
end Formalism.CountingSumsFrames.Har4
