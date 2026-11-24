-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.closedW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:40:46.153967+00:00
-- url     : https://prove2.me/submissions/72b059a9-5835-49ab-8d3d-12e261e4f5d0

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
theorem _root_.solution : ClosedW := by
  intro k r z
  have h := closed_stab k r (Set.range (fun a => bvec (eI k r a)) ∪ Set.range (fun a => bvec (esI k r a)) ∪ {z})
  convert h using 1
  ext g
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    rintro v ((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl)
    · exact (h2 a).1
    · exact (h2 a).2
    · exact h3
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a => ⟨h2 _ (Or.inl (Or.inl ⟨a, rfl⟩)), h2 _ (Or.inl (Or.inr ⟨a, rfl⟩))⟩, h2 _ (Or.inr rfl)⟩
end Formalism.FourierDecayAlt.P.B2x3
