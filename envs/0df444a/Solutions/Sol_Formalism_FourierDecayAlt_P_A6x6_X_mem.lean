-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.X_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:16.12169+00:00
-- url     : https://prove2.me/submissions/8ef73bff-c56b-409e-baf4-fe4a163db9eb

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
theorem _root_.solution (k : Fin m) : (X k : MvPolynomial (Fin m) ℚ) ∈ idealOfVars (Fin m) ℚ :=
  Ideal.subset_span ⟨k, rfl⟩
end Formalism.FourierDecayAlt.P.A6x6
