-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.qr_capSing_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:11:58.448334+00:00
-- url     : https://prove2.me/submissions/017d1fdd-1cb9-428f-beea-ea82f9c080ff

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_sdec_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_hw_cpol
import Theorems.Thm_Formalism_FourierDecayAlt_P_separating_polynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_capelli_stabilizer

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (hD : Qr.SingDom) (hX : Qr.ExistsSingMax) : Qr.CapSing := by
  intro V _ _ _ n E m hE hne
  obtain ⟨ν, v, hv, hv0, hw, _⟩ := hX V n E hE (CapSp E m) (capelli_stabilizer V n E m hE).1 hne
  refine ⟨(separating_polynomials n m _ (hw_cpol hE hv hv0 hw) (sdec_shift (hD V n E ν v hE hw hv0))).1, ?_⟩
  intro hm ν' v' hv' hv0' hw' j
  have h := (separating_polynomials n m _ (hw_cpol hE hv' hv0' hw') (sdec_shift (hD V n E ν' v' hE hw' hv0'))).2 hm
  have h2 : m j = ν' j - ((j : ℕ) : ℂ) := congrFun h j
  rw [h2]
  ring
end Formalism.FourierDecayAlt.P
