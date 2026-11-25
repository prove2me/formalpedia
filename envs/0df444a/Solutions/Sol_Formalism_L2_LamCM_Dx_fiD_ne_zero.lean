-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.fiD_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:06.116679+00:00
-- url     : https://prove2.me/submissions/b7565c60-44fe-4225-9c21-2fac04ccfdc8

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_castSucc
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_last
import Theorems.Thm_Formalism_L2_LamCM_Dx_lastL_apply
import Theorems.Thm_Formalism_L2_LamCM_Dx_coe_fiD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.LamCM.Dx.snocL_castSucc
attribute [local simp] Formalism.L2.LamCM.Dx.snocL_last
attribute [local simp] Formalism.L2.LamCM.Dx.lastL_apply

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.Dx
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.Dx
theorem _root_.solution {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) (hM : Sand M) : fiD M ≠ 0 := by
  obtain ⟨a, ha, hs⟩ := hM.1
  intro h0
  have hmem : (Matrix.of fun i => (Pi.single i (algebraMap (𝓞 K) K a) : Fin n → K)).det ∈ (fiD M : Submodule (𝓞 K) K) := by
    rw [coe_fiD M hM]; exact Submodule.subset_span ⟨_, hs, rfl⟩
  rw [h0] at hmem
  have hdiag : (Matrix.of fun i => (Pi.single i (algebraMap (𝓞 K) K a) : Fin n → K)) =
      Matrix.diagonal fun _ => algebraMap (𝓞 K) K a := by
    ext i j; simp [Pi.single_apply, Matrix.diagonal_apply, eq_comm]
  rw [hdiag, Matrix.det_diagonal, Finset.prod_const] at hmem
  have := (FractionalIdeal.mem_zero_iff _).1 hmem
  exact pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha) this
end Formalism.L2.LamCM.Dx
