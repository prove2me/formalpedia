-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.mid_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:11:57.533267+00:00
-- url     : https://prove2.me/submissions/48a0240b-f986-4937-9a20-2892cec0df09

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mid_levPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) : mid k r' p ↔ p ∈ Set.range (levPos k 1 r') := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 := h
    exact ⟨⟨p.val - 1, by omega⟩, Fin.ext (show p.val - 1 + 1 = p.val by omega)⟩
  · rintro ⟨s, rfl⟩
    exact mid_levPos k r' s
end Formalism.FourierDecayAlt.P.B2x2
