-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unipotent_map_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:20:39.820666+00:00
-- url     : https://prove2.me/submissions/6f58ea71-3a7f-4ff8-a086-7a6940407665

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_uMap_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_colEq
import Theorems.Thm_Formalism_QuantumDeterminants_S_F
import Theorems.Thm_Formalism_QuantumDeterminants_UW_F


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.UMapFrame := by
  intro k r z hz
  refine ⟨fun s hs => ?_, fun h hh => ?_⟩
  · obtain ⟨U, hU1, hU2, hsF⟩ := S_F hz.1 hs
    have hu := uMap_eq hz s U (colEq hsF)
    refine ⟨by rw [hu]; exact colEq hsF, by rw [hu]; exact ⟨fun i j h => hU1 i j h, hU2⟩, fun t ht => ?_⟩
    obtain ⟨Ut, _, _, htF⟩ := S_F hz.1 ht
    have hut := uMap_eq hz t Ut (colEq htF)
    have hst : s * t * Fm k r z = Fm k r z * (U * Ut) := by
      rw [Matrix.mul_assoc, htF, ← Matrix.mul_assoc, hsF, Matrix.mul_assoc]
    rw [uMap_eq hz (s * t) (U * Ut) (colEq hst), hu, hut]
  · have h1 : h * Fm k r z = Fm k r z * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
      rw [UW_F hh, Matrix.mul_one]
    exact uMap_eq hz h 1 (colEq h1)
end Formalism.FourierDecayAlt.P
