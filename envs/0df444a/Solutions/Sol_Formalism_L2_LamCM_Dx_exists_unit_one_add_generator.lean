-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.exists_unit_one_add_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:50:07.976238+00:00
-- url     : https://prove2.me/submissions/ffc58a4b-876a-455c-bf50-a774b2f88248

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_castSucc
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_last
import Theorems.Thm_Formalism_L2_LamCM_Dx_lastL_apply
import Theorems.Thm_Formalism_L2_LamCM_Dx_imI_ne_zero
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
theorem _root_.solution {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) :
    ∃ z : Fin (n+1) → K, z (Fin.last n) = 1 ∧ ∀ q ∈ M.map (lastL K n), q • z ∈ M := by
  set I := imI M hM
  have hI : I * I⁻¹ = 1 := mul_inv_cancel₀ (imI_ne_zero M hM)
  let T : Submodule (𝓞 K) K :=
    { carrier := {t | ∃ z : Fin (n+1) → K, z (Fin.last n) = t ∧ ∀ q ∈ M.map (lastL K n), q • z ∈ M}
      add_mem' := by
        rintro s t ⟨z, hz, hzM⟩ ⟨w, hw, hwM⟩
        exact ⟨z + w, by simp [hz, hw], fun q hq => by rw [smul_add]; exact M.add_mem (hzM q hq) (hwM q hq)⟩
      zero_mem' := ⟨0, by simp, fun q _ => by simp⟩
      smul_mem' := by
        rintro c t ⟨z, hz, hzM⟩
        refine ⟨c • z, by simp [hz], fun q hq => ?_⟩
        rw [smul_comm]; exact M.smul_mem c (hzM q hq) }
  have hle : ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ T := by
    rw [FractionalIdeal.coe_mul, Submodule.mul_le]
    intro p hp c hc
    obtain ⟨y, hy, rfl⟩ := hp
    refine ⟨c • y, by simp [mul_comm], fun q hq => ?_⟩
    have hqc : q * c ∈ I * I⁻¹ := FractionalIdeal.mul_mem_mul hq hc
    rw [hI] at hqc
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hqc
    rw [smul_smul, ← hr, algebraMap_smul]
    exact M.smul_mem r hy
  have h1 : (1 : K) ∈ ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [hI]; exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  obtain ⟨z, hz, hzM⟩ := hle h1
  exact ⟨z, hz, hzM⟩
end Formalism.L2.LamCM.Dx
