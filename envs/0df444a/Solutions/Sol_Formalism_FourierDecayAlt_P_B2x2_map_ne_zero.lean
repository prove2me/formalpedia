-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.map_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:47:24.107719+00:00
-- url     : https://prove2.me/submissions/3010387d-9df3-448b-aaaa-41b058162a61

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
theorem _root_.solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (h : μ ≠ 0) : μ.map f ≠ 0 := by
  intro h0
  apply h
  have h1 : (μ.map f) Set.univ = 0 := by simp [h0]
  rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ] at h1
  exact Measure.measure_univ_eq_zero.1 h1
end Formalism.FourierDecayAlt.P.B2x2
