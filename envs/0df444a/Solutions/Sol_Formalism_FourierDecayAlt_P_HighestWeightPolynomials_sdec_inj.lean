-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:44.529622+00:00
-- url     : https://prove2.me/submissions/b4266781-a8aa-4b71-a37c-774f945c2c7b

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_sdec_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HighestWeightPolynomials
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.HighestWeightPolynomials
theorem _root_.solution {n : ℕ} {m : Fin n → ℂ} (hm : SDec m) : Function.Injective m := by
  intro a b hab
  exact (sdec_re hm).injective (congrArg Complex.re hab)
end Formalism.FourierDecayAlt.P.HighestWeightPolynomials
