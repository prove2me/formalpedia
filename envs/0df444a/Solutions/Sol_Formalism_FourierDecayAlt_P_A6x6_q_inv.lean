-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.q_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:59.928632+00:00
-- url     : https://prove2.me/submissions/6af53286-8be7-415a-aee2-70ee3ab951b1

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_PL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_gaussF_of_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_PL_le

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
theorem _root_.solution (hInv : LatInvN Λ (gaussF ψ L M)) {x l : Fin m → K} (hx : x ∈ PL L m)
    (hl : l ∈ PL Λ m) :
    ψ (Ring.inverse 2 * ((x + l) ⬝ᵥ M *ᵥ (x + l))) = ψ (Ring.inverse 2 * (x ⬝ᵥ M *ᵥ x)) := by
  have h1 := hInv x l (mem_PL.1 hl)
  rwa [gaussF_of_mem ψ hx, gaussF_of_mem ψ ((PL L m).add_mem hx (PL_le hInv hl))] at h1
end Formalism.FourierDecayAlt.P.A6x6
