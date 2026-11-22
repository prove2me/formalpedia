-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.glAct_X_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:55.671184+00:00
-- url     : https://prove2.me/submissions/d5944abd-94c9-425d-a8b0-9f4b6e1b0f7b

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

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
theorem _root_.solution {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (i : Fin k) :
    glAct g (X (Sum.inl i)) = ∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j) := by
  simp only [glAct, aeval_X, Sum.elim_inl]
end Formalism.CountingSumsFrames.Har4
