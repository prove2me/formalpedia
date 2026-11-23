-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.dualMap_bijective_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:02.23578+00:00
-- url     : https://prove2.me/submissions/e269ffce-d232-4f91-932b-97d644e996e0

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_mulLeft_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_mulLat_inv_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_dualMap_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_card_addChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution {A : AddSubgroup K} (hA : perp ψ A = A) (b : Kˣ)
    (hfin : (mulLat (b : K) A).relIndex A ≠ 0) :
    Function.Bijective (dualMap ψ A (mulLat (b : K) A)) := by
  have : Finite (A ⧸ (mulLat (b : K) A).addSubgroupOf A) := Nat.finite_of_card_ne_zero hfin
  refine (dualMap_injective hA _).bijective_of_nat_card_le ?_
  rw [card_addChar]
  apply le_of_eq
  show (mulLat (b : K) A).relIndex A = A.relIndex (perp ψ (mulLat (b : K) A))
  rw [perp_mulLat, hA]
  have h := AddSubgroup.relIndex_map_map_of_injective (mulLat (b : K) A) A
    (mulLeft_injective (b⁻¹ : Kˣ))
  have h2 : (mulLat (b : K) A).map (AddMonoidHom.mulLeft ((b⁻¹ : Kˣ) : K)) = A :=
    mulLat_inv_mulLat b A
  rw [h2] at h
  exact h.symm
end Formalism.FourierDecayAlt.P.A6x3
