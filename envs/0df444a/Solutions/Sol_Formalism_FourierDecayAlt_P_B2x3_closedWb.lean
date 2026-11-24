-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.closedWb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:01:27.027438+00:00
-- url     : https://prove2.me/submissions/8793ab98-5242-4979-9912-248954a3239c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_closed_stab

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
theorem _root_.solution : ClosedWb := by
  intro k r
  have h := closed_stab k r (Set.range (fun a => bvec (eI k r a)) ∪ Set.range (fun a => bvec (esI k r a)))
  convert h using 1
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro v (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact (h2 a).1
    · exact (h2 a).2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a => ⟨h2 _ (Or.inl ⟨a, rfl⟩), h2 _ (Or.inr ⟨a, rfl⟩)⟩⟩
end Formalism.FourierDecayAlt.P.B2x3
