-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.psi_q_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:42.475079+00:00
-- url     : https://prove2.me/submissions/8f3b9226-201c-49a2-9abe-fa05f6130149

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_q_add

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
theorem _root_.solution (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (x y : Fin m → K) :
    ψ (Ring.inverse 2 * ((x + y) ⬝ᵥ M *ᵥ (x + y))) =
      ψ (Ring.inverse 2 * (x ⬝ᵥ M *ᵥ x)) * ψ (Ring.inverse 2 * (y ⬝ᵥ M *ᵥ y)) *
        ψ (x ⬝ᵥ M *ᵥ y) := by
  have h := Ring.inverse_mul_cancel 2 h2
  have e : Ring.inverse 2 * ((x + y) ⬝ᵥ M *ᵥ (x + y)) =
      Ring.inverse 2 * (x ⬝ᵥ M *ᵥ x) + Ring.inverse 2 * (y ⬝ᵥ M *ᵥ y) + x ⬝ᵥ M *ᵥ y := by
    rw [q_add hM]; linear_combination (x ⬝ᵥ M *ᵥ y) * h
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
end Formalism.FourierDecayAlt.P.A6x6
