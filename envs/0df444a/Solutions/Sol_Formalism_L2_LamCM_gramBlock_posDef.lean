-- Prove2me | solution 1 for Formalism.L2.LamCM.gramBlock_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:19:33.845874+00:00
-- url     : https://prove2.me/submissions/46637a2f-bd27-481a-accc-c11ec4d985ee

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_HermitianFormGramBlockBasis
import Theorems.Thm_Formalism_L2_LamCM_gramBlock_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain IsLocalRing Matrix
open scoped nonZeroDivisors ComplexOrder
variable {K : Type} [Field K] [NumberField K] {B : Type} {m : B → ℕ} {g : ℕ}
namespace Formalism.L2.LamCM
theorem _root_.solution (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K)
    (H : Matrix (Fin g) (Fin g) ℂ) (σ : K →+* ℂ) (b : B) (hH : H.PosDef) (hU : U.det ≠ 0) :
    (gramBlock e U H σ b).PosDef := by
  classical
  rw [gramBlock_eq]
  refine hH.conjTranspose_mul_mul_same ?_
  rw [Matrix.mulVec_injective_iff]
  have hdet : (U.map σ).det ≠ 0 := by
    rw [show U.map σ = σ.mapMatrix U from rfl, ← RingHom.map_det]
    exact (map_ne_zero σ).mpr hU
  have hli : LinearIndependent ℂ (U.map σ).row :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hinj : Function.Injective (fun j : Fin (m b) => e ⟨b, j⟩) := fun j j' h =>
    eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h)).2
  exact hli.comp _ hinj
end Formalism.L2.LamCM
