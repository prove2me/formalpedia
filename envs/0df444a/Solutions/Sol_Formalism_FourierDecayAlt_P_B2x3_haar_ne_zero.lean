-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.haar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:21:19.144463+00:00
-- url     : https://prove2.me/submissions/9b0e4797-fa12-4430-90f2-fba3e6e99f28

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [MeasurableSpace Γ]
    (m : Measure Γ) [m.IsOpenPosMeasure] : m ≠ 0 := by
  intro h
  have := isOpen_univ.measure_pos m ⟨1, trivial⟩
  rw [h] at this
  simp at this
end Formalism.FourierDecayAlt.P.B2x3
