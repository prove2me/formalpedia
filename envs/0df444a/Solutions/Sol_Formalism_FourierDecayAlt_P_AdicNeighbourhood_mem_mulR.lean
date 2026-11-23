-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.mem_mulR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:36.729835+00:00
-- url     : https://prove2.me/submissions/36129550-43ec-4006-8346-20b53d53dd09

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
theorem _root_.solution {R : Subring K} {ν x : K} : x ∈ mulR R ν ↔ ∃ r ∈ R, x = ν * r := by
  unfold mulR
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨r, hr, e⟩; exact ⟨r, hr, e.symm⟩
  · rintro ⟨r, hr, e⟩; exact ⟨r, hr, e.symm⟩
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
