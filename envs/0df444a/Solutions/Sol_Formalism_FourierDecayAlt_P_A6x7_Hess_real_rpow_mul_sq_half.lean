-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Hess.real_rpow_mul_sq_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:05.066556+00:00
-- url     : https://prove2.me/submissions/ee137d3c-9842-46da-9df3-fa4afa3409be

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
theorem _root_.solution (B C : ℝ) (hB : 0 < B) (hC : 0 < C) (m : ℕ) :
    (B * C ^ 2) ^ ((m : ℝ) / 2) = B ^ ((m : ℝ) / 2) * C ^ m := by
  rw [Real.mul_rpow hB.le (by positivity), ← Real.rpow_natCast C 2, ← Real.rpow_mul hC.le,
    ← Real.rpow_natCast C m]
  congr 2
  push_cast
  ring
end Formalism.FourierDecayAlt.P.A6x7.Hess
