-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.glAct_glAct_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:44.79411+00:00
-- url     : https://prove2.me/submissions/14ed3205-d8d4-4a03-8625-9aa6a5a905e8

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_inv_glAct

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
theorem _root_.solution {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (f : PolXY K k) :
    glAct g (glAct g⁻¹ f) = f := by
  simpa using glAct_inv_glAct g⁻¹ f
end Formalism.CountingSumsFrames.Har4
