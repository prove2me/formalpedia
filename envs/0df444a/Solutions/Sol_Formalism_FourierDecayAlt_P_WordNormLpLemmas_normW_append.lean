-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordNormLpLemmas.normW_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:40:43.832434+00:00
-- url     : https://prove2.me/submissions/12ce212b-6bd1-41a9-805a-ee5bb6276eee

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialDegreeExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremCorollary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordNormLpLemmas
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas Formalism.FourierDecayAlt.P.RealWeightedForms
  Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.WordNormLpLemmas
theorem _root_.solution {S : Type} (nn : ℝ → ℝ) (L w : List (Letter ℂ S)) :
    normW nn (L ++ w) = normW nn L * normW nn w := by
  unfold normW; rw [List.map_append, List.prod_append]
end Formalism.FourierDecayAlt.P.WordNormLpLemmas
