-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.two_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:37.223626+00:00
-- url     : https://prove2.me/submissions/8df317c0-10fc-4ff3-8267-d136b1c68ae0

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open MvPolynomial
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution : (2 : MvPolynomial (Fin m) ℚ) * C (1 / 2 : ℚ) = 1 := by
  have : (2 : MvPolynomial (Fin m) ℚ) = C 2 := (map_ofNat C 2).symm
  rw [this, ← C_mul]; norm_num
end Formalism.FourierDecayAlt.P.A6x6
