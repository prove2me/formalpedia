-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.reps_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:25.389197+00:00
-- url     : https://prove2.me/submissions/6a55699b-a3ad-4cf1-acf2-7c9f258820bd

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution {L₁ L₂ : AddSubgroup K} {S : Finset K} (hS : IsReps S L₂ L₁) :
    S.Nonempty := by
  obtain ⟨a, ha, _⟩ := hS.2 0 L₂.zero_mem
  exact ⟨a, ha.1⟩
end Formalism.FourierDecayAlt.P.A6x4
