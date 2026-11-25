-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:46.210019+00:00
-- url     : https://prove2.me/submissions/9742a23b-08d5-44c5-83eb-81c1f55b014c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_IsUnitDetOfUnitary
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_fnOfV_one_apply
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_eval_famAct
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_fnOfV_injective
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_isUnit_det_of_unitary
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution : Transfer := by
  intro ι _ n G hG lam W hW hne hinv
  set φ := fnOfV G (shiftOfV lam) 1 with hφ
  have hinj : Function.Injective φ := fun P Q hPQ => by
    have h0 : φ (P - Q) = 0 := by rw [map_sub, hPQ, sub_self]
    exact sub_eq_zero.mp (fnOfV_injective G _ _ h0)
  refine ⟨W.comap φ ⊓ CSpanV lam, inf_le_right, ?_, ?_, ?_⟩
  · obtain ⟨F, hFW, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨P, hP, rfl⟩ := hW hFW
    intro hbot
    have hPM : P ∈ W.comap φ ⊓ CSpanV lam := Submodule.mem_inf.mpr ⟨hFW, hP⟩
    rw [hbot, Submodule.mem_bot] at hPM
    exact hF0 (by rw [hPM, map_zero])
  · intro g hg P hPM
    obtain ⟨hPW, hPC⟩ := Submodule.mem_inf.mp hPM
    have hPW' : φ P ∈ W := Submodule.mem_comap.mp hPW
    obtain ⟨F', hF'W, hF'⟩ := hinv g hg (φ P) hPW'
    have hdet : ∀ τ, IsUnit (g τ).det := fun τ => isUnit_det_of_unitary (hG τ) (hg τ)
    set cst : ℂ := ∏ τ, (g τ).det ^ (shiftOfV lam τ) with hcst
    have hcst0 : cst ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hdet τ).ne_zero
    have key : φ (famAct g P) = cst⁻¹ • F' := by
      funext y
      obtain ⟨y', hy'0⟩ : ∃ y' : FramesV G, ∀ τ, y'.1 τ = g τ * y.1 τ :=
        ⟨⟨fun τ => g τ * y.1 τ, fun τ => by
          rw [Matrix.det_mul]
          exact (hdet τ).mul (y.2 τ)⟩, fun _ => rfl⟩
      have hy' := hF' y y' hy'0
      show _ = cst⁻¹ * F' y
      rw [hy', hφ, fnOfV_one_apply, fnOfV_one_apply, eval_famAct]
      simp only [hy'0, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_apply]
      rw [← hcst]
      field_simp
    have hmemW : φ (famAct g P) ∈ W := by
      rw [key]
      exact W.smul_mem _ hF'W
    obtain ⟨P', hP'C, hP'⟩ := hW hF'W
    have hfam : famAct g P = cst⁻¹ • P' := hinj (by rw [key, map_smul, hP'])
    refine Submodule.mem_inf.mpr ⟨hmemW, ?_⟩
    rw [hfam]
    exact (CSpanV lam).smul_mem _ hP'C
  · intro hle
    apply le_antisymm hW
    rintro F ⟨P, hP, rfl⟩
    exact (Submodule.mem_inf.mp (hle hP)).1
end Formalism.L2.SG.Pf.ColDictValCPf
