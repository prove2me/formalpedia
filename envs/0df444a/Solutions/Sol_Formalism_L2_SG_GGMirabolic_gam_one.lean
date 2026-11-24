-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.gam_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:25:35.565796+00:00
-- url     : https://prove2.me/submissions/6ce0d87f-d8a6-4c79-819c-43938a50647b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicBase
import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_isUni_one
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_superdiag_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic
open Finset Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Classical
variable {F : Type} [Field F] [Fintype F] (k : ℕ)
variable {k}
namespace Formalism.L2.SG.GGMirabolic
theorem _root_.solution (ψ₀ : AddChar F ℂ) :
    gam ψ₀ (1 : GL (Fin k) F) = (Fintype.card (GL (Fin k) F) : ℂ) / (cardU F k : ℂ) := by
  have hp : ∀ y : GL (Fin k) F, psiNat ψ₀ (y * 1 * y⁻¹) = 1 := by
    intro y
    rw [mul_one, mul_inv_cancel]
    simp only [psiNat, isUni_one, if_true, psiU, Units.val_one, superdiag_one, AddChar.map_zero_eq_one]
  unfold gam
  rw [Finset.sum_congr rfl (fun y _ => hp y)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [div_eq_inv_mul]
end Formalism.L2.SG.GGMirabolic
