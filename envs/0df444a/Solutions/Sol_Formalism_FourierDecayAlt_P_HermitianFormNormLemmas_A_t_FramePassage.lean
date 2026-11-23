-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A.t_FramePassage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:01.411224+00:00
-- url     : https://prove2.me/submissions/6d9db60b-903e-49ad-bcc4-cc0bedc759fb

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_A_book_constants_pos_of_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
theorem _root_.solution : FramePassage := by
  intro P _ B rd g r k f Irat Ire hPos hJac hFr
  obtain ⟨hrd, hg, F1, F2, F3⟩ := hFr
  obtain ⟨hGam, hμK, hμKpp, hμSpp, hμSpp', hMM, hU, hc0, hc0', htt, hAA, hD⟩ := book_constants_pos_of_pos B hPos
  have hvolZZ : 0 < B.volZZ := hPos.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvolPP : 0 < B.volPP := hPos.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold S3.MassData.InJacMod at hJac
  have hexp : rd ^ (((f * (r + 1) * (8 * r ^ 2 + 10 * r + 3) : ℕ) : ℝ) / 3)
      = rd ^ (f * (r + 1)) * rd ^ (((f * r * (r + 1) * (8 * r + 10) : ℕ) : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hrd]
    congr 1
    push_cast
    ring
  have h1 : (B.c0 * B.c0')⁻¹ * B.IntN = (B.unitLevelVolume / B.volZZ)⁻¹ * ((B.c0 * B.c0')⁻¹ * B.IntC) := by
    rw [hJac]
    field_simp
  have hpb : 0 < rd ^ (((f * r * (r + 1) * (8 * r + 10) : ℕ) : ℝ) / 3) := Real.rpow_pos_of_pos hrd _
  rw [h1, F1, F2, F3, hexp, div_pow]
  have h2 : (0 : ℝ) < 2 ^ (f * (r + 1)) := by positivity
  have h3 : 0 < rd ^ (f * (r + 1)) := by positivity
  have h4 : 0 < g ^ (f * (r + 1) * (2 * r + 3)) := by positivity
  field_simp
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
