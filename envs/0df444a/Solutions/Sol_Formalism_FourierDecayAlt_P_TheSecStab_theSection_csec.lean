-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:53:05.815224+00:00
-- url     : https://prove2.me/submissions/e7f7af52-8133-4a2b-8f7f-8684c085925e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_stab_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSec_theSection_isSection


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TheSecStab
theorem _root_.solution (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') :
    IsSection k r z z' (theSection k r z z') ∧ ∀ ζ ζ' : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
      Tz k r z * Tz k r z' < Complex.normSq ζ' →
        NF.Stab k r z z' (theSection k r z z') ζ = NF.Stab k r z z' (theSection k r z z') ζ' :=
  ⟨theSection_isSection k r z z' hk hz hz' hT hT', fun ζ ζ' hζ hζ' => Set.ext fun p =>
    ⟨stab_sub hk hz hz' hT hT' hζ hζ' p, stab_sub hk hz hz' hT hT' hζ' hζ p⟩⟩
end Formalism.FourierDecayAlt.P.TheSecStab
