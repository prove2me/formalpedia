-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.half_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:45.239663+00:00
-- url     : https://prove2.me/submissions/4c60753b-254c-4855-96b0-c8919bcb5345

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (A : ℝ) (hA : 0 < A) (m : ℕ) :
    A ^ ((m : ℝ) ^ 2 / 2) * A ^ ((m : ℝ) ^ 2 / 2) = A ^ (m ^ 2) := by
  rw [← Real.rpow_add hA, ← Real.rpow_natCast A (m ^ 2)]
  congr 1
  push_cast
  ring
end Formalism.FourierDecayAlt.P.GermSumLattices
