-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.ae_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:47:19.399844+00:00
-- url     : https://prove2.me/submissions/cc2aed89-4c80-4220-9f17-32f3f6c28faf

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
theorem _root_.solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (s : Set Y) (h : ν sᶜ = 0) : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ s := by
  rw [ae_iff]
  have e : {p : X × Y | ¬ p.2 ∈ s} = Set.univ ×ˢ sᶜ := by
    ext p
    simp
  rw [e, Measure.prod_prod, h, mul_zero]
end Formalism.FourierDecayAlt.P.B2x2
