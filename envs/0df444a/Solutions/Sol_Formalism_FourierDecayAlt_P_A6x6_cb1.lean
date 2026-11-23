-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.cb1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:09.410656+00:00
-- url     : https://prove2.me/submissions/32d5f964-7c70-4903-b599-71dd8ec332ba

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_symm_dot
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_cb2

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
variable {L Λ : AddSubgroup K}
variable {ψ}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hInv : LatInvN Λ (gaussF ψ L M))
    {x x' u : Fin m → K} (hu : u ∈ PL L m) (hl : x - x' ∈ PL Λ m) :
    ψ (x ⬝ᵥ M *ᵥ u) = ψ (x' ⬝ᵥ M *ᵥ u) := by
  rw [symm_dot hM u x, symm_dot hM u x', cb2 h2 hM hInv hu hl]
end Formalism.FourierDecayAlt.P.A6x6
