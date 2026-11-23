-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.e_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:00.806167+00:00
-- url     : https://prove2.me/submissions/4a2df40b-ffec-4607-8f2d-6b7cd17fc5a7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_X_mem

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
theorem _root_.solution (s : Finset (Fin m)) :
    (∑ k ∈ s, X k : MvPolynomial (Fin m) ℚ) ∈ idealOfVars (Fin m) ℚ :=
  Ideal.sum_mem _ fun k _ => X_mem k
end Formalism.FourierDecayAlt.P.A6x6
