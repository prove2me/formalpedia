-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.cb2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:43.675559+00:00
-- url     : https://prove2.me/submissions/3a7ec301-98d6-4bb1-8335-b548b88ae45e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_b_one

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
    ψ (u ⬝ᵥ M *ᵥ x) = ψ (u ⬝ᵥ M *ᵥ x') := by
  have e : x = x' + (x - x') := by abel
  rw [e, mulVec_add, dotProduct_add, AddChar.map_add_eq_mul, b_one h2 hM hInv hu hl, mul_one]
end Formalism.FourierDecayAlt.P.A6x6
