-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.two_le_H
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:05.398918+00:00
-- url     : https://prove2.me/submissions/b057791a-9e61-46aa-a7d7-54c19ea3917e

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
variable {Cl Nu : Type}
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
theorem _root_.solution (L : LocalNG Cl Nu) (hb : L.Basic) (p : L.P) (hp : p ∈ L.Om) : 2 ≤ L.H p := by
  unfold LocalNG.Basic at hb
  obtain ⟨_, _, hq, hqH, _⟩ := hb
  have h2 : (2 : ℝ) ≤ (L.q p : ℝ) := by exact_mod_cast hq p
  exact h2.trans (hqH p hp)
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
