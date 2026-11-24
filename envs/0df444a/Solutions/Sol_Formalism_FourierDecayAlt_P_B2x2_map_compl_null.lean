-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.map_compl_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:59:11.277994+00:00
-- url     : https://prove2.me/submissions/91f00a09-bb73-4c20-90be-9bb097aecdcc

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
theorem _root_.solution {X : Type*} [MeasurableSpace X] {k r : ℕ} (V : Set (Mat k r)) (hV : IsClosed V) (μ : Measure X)
    (f : X → Mt k r) (hf : Measurable f) (h : μ {x | f x ∉ V} = 0) : (μ.map f) Vᶜ = 0 := by
  have hm : MeasurableSet (Vᶜ : Set (Mt k r)) :=
    (show IsOpen (Vᶜ : Set (Mt k r)) from hV.isOpen_compl).measurableSet
  rw [Measure.map_apply hf hm]
  exact h
end Formalism.FourierDecayAlt.P.B2x2
