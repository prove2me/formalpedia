-- Prove2me | solution 1 for Formalism.L2.Th1.H.FourthRoot_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:04.582733+00:00
-- url     : https://prove2.me/submissions/a2ac203f-c19c-4ae1-a3f5-d3e16c9a2b82

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Theorems.Thm_Formalism_L2_Th1_H_blockSlice_fourfoldMk
import Theorems.Thm_Formalism_L2_Th1_H_fourfoldTensor_smul
import Theorems.Thm_Formalism_L2_Th1_H_restrict_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (h4 : Tens4Mem) : FourthRoot := by
  intro n _ h Λ α hα0 P hP hP0 hline
  obtain ⟨z, hz⟩ : ∃ z, P z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hP0 (funext hcon)
  have key_line : ∀ θ ∈ Th (matH h) α Λ, tens4 θ = P → ∀ F ∈ Th (matH h) α Λ, ∃ c : ℂ, F = c • θ := by
    intro θ hθ hθP F hF
    have hw : θ (slice 0 z) ≠ 0 := by
      intro h0
      apply hz
      rw [← hθP]
      exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4)) h0
    obtain ⟨c, hc⟩ := hline _ (h4 n h Λ α (fun a => if a = 0 then F else θ)
      (by intro a; split_ifs <;> assumption))
    refine ⟨c, funext fun v => ?_⟩
    have h1 := congrFun hc (mk4 (fun a => if a = 0 then v else slice 0 z))
    rw [← hθP] at h1
    simp only [Pi.smul_apply, smul_eq_mul, tens4, Fin.prod_univ_four, blockSlice_fourfoldMk] at h1
    simp only [if_true, Fin.isValue, one_ne_zero, if_false, Fin.reduceEq] at h1
    have h3 : θ (slice 0 z) * θ (slice 0 z) * θ (slice 0 z) ≠ 0 := mul_ne_zero (mul_ne_zero hw hw) hw
    apply mul_right_cancel₀ h3
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination h1
  refine ⟨?_, fun θ hθ hθP => ⟨?_, key_line θ hθ hθP⟩⟩
  · set z₁ : Fin 4 × n → ℂ := fun p => if p.1 = 0 then 0 else z p with hz₁def
    have hz₁ : slice 0 z₁ = 0 := by
      funext i
      simp [slice, hz₁def]
    have hzz : z₁ + emb0 (slice 0 z) = z := by
      funext p
      by_cases hp : p.1 = 0
      · have : p = (0, p.2) := Prod.ext hp rfl
        simp only [Pi.add_apply, hz₁def, emb0, LinearMap.coe_mk, AddHom.coe_mk, hp, if_true, slice,
          zero_add]
        rw [← this]
      · simp [hz₁def, emb0, hp]
    have hθ₁ := restrict_mem h Λ α hα0 hP z₁ hz₁
    set θ₁ : (n → ℂ) → ℂ := fun v => P (z₁ + emb0 v) with hθ₁def
    obtain ⟨c, hc⟩ := hline _ (h4 n h Λ α (fun _ => θ₁) (fun _ => hθ₁))
    have hc' : tens4 θ₁ = c • P := hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h1 := congrFun hc' (mk4 fun _ => slice 0 z)
      simp only [tens4, blockSlice_fourfoldMk, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zero_smul,
        Pi.zero_apply, hθ₁def, hzz] at h1
      exact hz (pow_eq_zero_iff (by norm_num) |>.1 h1)
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) (n := 4) (by norm_num)
    refine ⟨r • θ₁, (Th (matH h) α Λ).smul_mem r hθ₁, ?_⟩
    rw [fourfoldTensor_smul, hr, hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]
  · intro θ' hθ' hθ'P
    obtain ⟨c, rfl⟩ := key_line θ hθ hθP θ' hθ'
    refine ⟨c, ?_, rfl⟩
    rw [fourfoldTensor_smul, hθP] at hθ'P
    have h1 := congrFun hθ'P z
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    exact mul_right_cancel₀ hz (by rw [h1, one_mul])
end Formalism.L2.Th1.H
