-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.inverse_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:54.98513+00:00
-- url     : https://prove2.me/submissions/99246a83-c230-40bd-b47f-777cf5038d1b

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
theorem _root_.solution {a b : K} (h : a * b = 1) : Ring.inverse a = b := by
  have := Ring.inverse_unit (⟨a, b, h, by rw [mul_comm]; exact h⟩ : Kˣ)
  simpa using this
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
