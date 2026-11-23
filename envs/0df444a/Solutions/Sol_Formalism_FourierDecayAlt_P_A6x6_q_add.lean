-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.q_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:09.654612+00:00
-- url     : https://prove2.me/submissions/e65e3886-5ea1-4315-8b9e-4bd39d8db167

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_symm_dot

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
open Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)
variable {M : Matrix (Fin m) (Fin m) K}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (hM : M.IsSymm) (x y : Fin m → K) :
    (x + y) ⬝ᵥ M *ᵥ (x + y) = x ⬝ᵥ M *ᵥ x + y ⬝ᵥ M *ᵥ y + 2 * (x ⬝ᵥ M *ᵥ y) := by
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, symm_dot hM x y]
  ring
end Formalism.FourierDecayAlt.P.A6x6
