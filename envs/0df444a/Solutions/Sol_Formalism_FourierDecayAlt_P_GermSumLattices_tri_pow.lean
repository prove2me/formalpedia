-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.tri_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:00.935372+00:00
-- url     : https://prove2.me/submissions/73c32919-4d64-4f95-893e-bc6cde45843b

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
theorem _root_.solution (A : ℝ) (m : ℕ) : (A * A) ^ (m * (m + 1) / 2) = A ^ (m ^ 2 + m) := by
  rw [← pow_two, ← pow_mul, Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self m)]
  congr 1
  ring
end Formalism.FourierDecayAlt.P.GermSumLattices
