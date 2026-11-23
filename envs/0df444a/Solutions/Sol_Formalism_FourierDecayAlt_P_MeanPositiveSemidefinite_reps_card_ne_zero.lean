-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.reps_card_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:05.828271+00:00
-- url     : https://prove2.me/submissions/254750ac-03f1-4906-99fe-c2a745e05528

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanPositiveSemidefinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
namespace Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
theorem _root_.solution {K : Type} [CommRing K] {S : Finset K} {L M : AddSubgroup K}
    (h : IsReps S L M) : S.card ≠ 0 := by
  obtain ⟨a, ha, _⟩ := h.2 0 L.zero_mem
  exact Finset.card_ne_zero_of_mem ha.1
end Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
