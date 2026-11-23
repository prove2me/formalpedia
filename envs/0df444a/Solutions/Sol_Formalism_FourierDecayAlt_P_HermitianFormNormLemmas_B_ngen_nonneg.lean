-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.ngen_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:22.273411+00:00
-- url     : https://prove2.me/submissions/a87cc2a1-844f-47f8-80d3-875d14b065e5

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
theorem _root_.solution (L : LocalNG Cl Nu) (C0 r : ℕ) (hb : L.Basic) (hM : L.MassRatioAt C0 r) (p : L.P) :
    0 ≤ L.ngen p := by
  unfold LocalNG.Basic at hb
  unfold LocalNG.MassRatioAt at hM
  obtain ⟨_, hH, _, _, hnn, _⟩ := hb
  by_cases hp : p ∈ L.Om
  · have h1 := hM.2 p hp
    have h2 := hnn p
    have hpos : 0 < 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) :=
      mul_pos (by norm_num) (pow_pos (by linarith [hH p]) _)
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hpos hneg
    linarith
  · rw [← hM.1 p hp]
    exact hnn p
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
