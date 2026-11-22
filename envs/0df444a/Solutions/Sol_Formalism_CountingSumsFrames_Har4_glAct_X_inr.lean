-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.glAct_X_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:30.750768+00:00
-- url     : https://prove2.me/submissions/195dd603-4d5e-4f66-a535-de1722bc6a66

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
    glAct g (X (Sum.inr i)) =
      ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * X (Sum.inr j) := by
  simp only [glAct, aeval_X, Sum.elim_inr]
end Formalism.CountingSumsFrames.Har4
