-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordNormLpLemmas.normW_Lp_dl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:39:44.537383+00:00
-- url     : https://prove2.me/submissions/0f75e80a-3477-4d80-bd28-0d6014ceeda6

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
theorem _root_.solution {S : Type} {K : ℕ} (nn : ℝ → ℝ) (sl : Fin K → S) (y : Fin K → ℝ) :
    normW nn ((Lp sl y).map dl) = ∏ a, nn (y a + 1) := by
  unfold normW Lp
  rw [List.map_ofFn, List.map_ofFn, List.prod_ofFn]
  simp [Function.comp_def, dl]
end Formalism.FourierDecayAlt.P.WordNormLpLemmas
