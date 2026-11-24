-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.ae_of_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:01:25.968085+00:00
-- url     : https://prove2.me/submissions/b934fd03-4c38-4511-84dd-2011c22c1c55

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists

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
theorem _root_.solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X) (h : μ sᶜ = 0) : ∀ᵐ x ∂μ, x ∈ s := by
  rw [ae_iff]
  exact h
end Formalism.FourierDecayAlt.P.B2x2
