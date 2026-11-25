-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSecStab.uwset_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:27:15.127251+00:00
-- url     : https://prove2.me/submissions/db511ecc-48e4-4893-9b98-9eccda76d935

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWb_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mulVec_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wbPart
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_wbPart_jV


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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : Mat k r} (hg : g ∈ UWset k r z) :
    ∃ μ ∈ UH (Hb k), g = embWb k r μ ∧ μ *ᵥ wbPart k r z = wbPart k r z := by
  obtain ⟨μ, hμ, rfl⟩ := (UWb_iff g).1 ⟨hg.1, hg.2.1⟩
  refine ⟨μ, hμ, rfl, ?_⟩
  have h1 : embWb k r μ *ᵥ z = z := hg.2.2
  rw [← jV_wbPart hz, emb_mulVec_jV] at h1
  have := congrArg (wbPart k r) h1
  rwa [wbPart_jV, wbPart_jV] at this
end Formalism.FourierDecayAlt.P.TheSecStab
