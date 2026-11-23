-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1.t_ExponentSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:14.526209+00:00
-- url     : https://prove2.me/submissions/0f79a16b-5720-4c6c-a38b-5d9e07f95b9d

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1
theorem _root_.solution : ExponentSum := by
  intro C1 C0 A r hA
  unfold e7 eN
  have h1 : r + 1 ≤ (r + 1) ^ 2 := by nlinarith
  generalize (r + 1) ^ 2 = s at *
  have hA2 : (C1 + C0 + 38) * s ≤ A * s := Nat.mul_le_mul_right _ hA
  nlinarith
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1
