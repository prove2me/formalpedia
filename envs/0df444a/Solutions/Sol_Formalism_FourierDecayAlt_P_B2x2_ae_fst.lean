-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.ae_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:47:17.339169+00:00
-- url     : https://prove2.me/submissions/062b1ab2-c0a7-4757-a2d8-98e5d3d40e63

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
    (s : Set X) (h : μ sᶜ = 0) : ∀ᵐ p ∂(μ.prod ν), p.1 ∈ s := by
  rw [ae_iff]
  have e : {p : X × Y | ¬ p.1 ∈ s} = sᶜ ×ˢ Set.univ := by
    ext p
    simp
  rw [e, Measure.prod_prod, h, zero_mul]
end Formalism.FourierDecayAlt.P.B2x2
