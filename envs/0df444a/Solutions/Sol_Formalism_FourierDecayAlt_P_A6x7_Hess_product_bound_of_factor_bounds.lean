-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Hess.product_bound_of_factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:05.024171+00:00
-- url     : https://prove2.me/submissions/760814c7-36c1-4d6c-85d3-79db8811dcc8

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice

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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Hess
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x7.Hess
theorem _root_.solution (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (m : ℕ) :
    (A * (B⁻¹) ^ m) ^ (-(1 : ℝ) / 2) = A ^ (-(1 : ℝ) / 2) * B ^ ((m : ℝ) / 2) := by
  rw [Real.mul_rpow hA.le (by positivity), ← Real.rpow_natCast, Real.inv_rpow hB.le,
    ← Real.rpow_neg hB.le, ← Real.rpow_mul hB.le]
  congr 2
  ring
end Formalism.FourierDecayAlt.P.A6x7.Hess
