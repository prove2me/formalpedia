-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.PL_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:26.545714+00:00
-- url     : https://prove2.me/submissions/58304c05-7ce6-4c7c-8fc0-0052aa225ad7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_PL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_psi_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_gaussF_of_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_gaussF_of_not_mem

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
theorem _root_.solution (hInv : LatInvN Λ (gaussF ψ L M)) : PL Λ m ≤ PL L m := by
  intro l hl
  by_contra h
  have h1 := hInv 0 l (mem_PL.1 hl)
  rw [zero_add, gaussF_of_not_mem ψ h, gaussF_of_mem ψ (PL L m).zero_mem] at h1
  exact psi_ne_zero ψ _ h1.symm
end Formalism.FourierDecayAlt.P.A6x6
