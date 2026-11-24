-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B1.core0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:22:45.649404+00:00
-- url     : https://prove2.me/submissions/59623581-e3a8-40c8-9585-b74c80633c6c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_coreC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B1
theorem _root_.solution : FormCore := by
  intro V _ _ W β βi hβ hβi hnn hle hW
  refine coreC V W β βi hβ hβi hnn hle ?_
  intro x hx
  obtain ⟨Φ, t₀, h0, hc, ht, U, hU, hae⟩ := hW x hx
  exact ⟨Φ, fun t => βi (Φ t) (Φ t), t₀, h0, by simp only [h0], hc, ht, U, hU, hae⟩
end Formalism.FourierDecayAlt.P.B1
