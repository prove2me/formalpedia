-- Prove2me | solution 1 for Formalism.L2.DIV.mem_transLat_gLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:56:17.14194+00:00
-- url     : https://prove2.me/submissions/346a4965-4539-452a-987b-9e395fa14870

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_isBasisAt_gLat
import Theorems.Thm_Formalism_L2_DIV_polyAction_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K) (F : Pol K ι n) :
    F ∈ transLat lam T (fun τ => gLat (g τ) (M τ)) ↔ actP lam g⁻¹ F ∈ transLat lam T M := by
  simp only [transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  constructor
  · intro h w B hB
    have h1 := h w (g * B) fun τ => (isBasisAt_gLat w (g τ) (B τ) (M τ)).mpr (hB τ)
    rwa [mul_inv_rev, polyAction_mul] at h1
  · intro h w B hB
    have h1 := h w (g⁻¹ * B) fun τ => (isBasisAt_gLat w (g τ) ((g⁻¹ * B) τ) (M τ)).mp (by
      have : g τ * (g⁻¹ * B) τ = B τ := by simp
      rw [this]
      exact hB τ)
    rwa [← polyAction_mul, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one] at h1
end Formalism.L2.DIV
