-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stabilizer_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:53:58.245201+00:00
-- url     : https://prove2.me/submissions/6ae51108-f582-4929-80db-64570c1a2c9d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_additive_character_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_character_additive
import Theorems.Thm_Formalism_FourierDecayAlt_P_stabilizer_block_point
import Theorems.Thm_Formalism_FourierDecayAlt_P_stabilizer_long_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.StabInvariant := by
  intro n β g l u k k' hg hl hu hk hk' hs
  have h0 : subSum k + superSum k' = 0 := by
    rcases hg with ⟨z, hz, rfl⟩ | ⟨t, c, ht, rfl⟩
    · exact (stabilizer_long_point n z hz k k' hk hk').2 hs
    · exact (stabilizer_block_point n t c ht k k' hk hk').2 hs
  constructor
  · calc l * k * g * (k' * u) = l * (k * g * k') * u := by simp only [Matrix.mul_assoc]
      _ = l * g * u := by rw [hs]
  · rw [(character_additive n l k).2 hl hk, (character_additive n k' u).1 hk' hu,
      ← (additive_character_psi β _ _).1, ← (additive_character_psi β _ _).1]
    congr 1
    linear_combination h0
end Formalism.FourierDecayAlt.P
