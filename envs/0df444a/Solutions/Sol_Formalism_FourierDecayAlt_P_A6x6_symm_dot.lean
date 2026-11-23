-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.symm_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:16.211914+00:00
-- url     : https://prove2.me/submissions/cbbce9e5-29a7-4566-b4f6-6701332ef5ef

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
open Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)
variable {M : Matrix (Fin m) (Fin m) K}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (hM : M.IsSymm) (x y : Fin m → K) : y ⬝ᵥ M *ᵥ x = x ⬝ᵥ M *ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]
end Formalism.FourierDecayAlt.P.A6x6
