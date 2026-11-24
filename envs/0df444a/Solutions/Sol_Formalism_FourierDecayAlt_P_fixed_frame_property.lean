-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.fixed_frame_property
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:55:17.074947+00:00
-- url     : https://prove2.me/submissions/9c148eae-d5a5-4325-9a34-79ea60c3b187

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_uMap_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_standard_flag_property
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_map_frame


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.FixFrame := by
  intro k r z hz
  ext g
  constructor
  · rintro ⟨hgV, hfix⟩
    have hS : g ∈ Sset k r z := by
      rw [← standard_flag_property k r z hz]
      exact ⟨hgV, fun a => by simp [hfix a]⟩
    refine ⟨hS, uMap_eq hz g 1 fun b => ?_⟩
    simp [Matrix.one_apply, hfix b]
  · rintro ⟨hS, hU⟩
    have hS' := hS
    rw [← standard_flag_property k r z hz] at hS'
    refine ⟨hS'.1, fun a => ?_⟩
    rw [((unipotent_map_frame k r z hz).1 g hS).1 a, hU]
    simp [Matrix.one_apply]
end Formalism.FourierDecayAlt.P
