-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.fnOfV_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:34.725044+00:00
-- url     : https://prove2.me/submissions/28d9a789-fbb9-453c-894a-c391bc5d9433

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_IsUnitDetOfUnitary
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_fnOfV_one_apply
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_eval_detBlocks
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_detBlocks_ne_zero
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
theorem _root_.solution (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (h : fnOfV G s 1 P = 0) : P = 0 := by
  have hz : detBlocks (ι := ι) (n := n) * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero, eval_detBlocks]
    by_cases hx : ∀ τ, (Matrix.of fun a b : Fin n => x (τ, a, b)).det ≠ 0
    · obtain ⟨y0, hy0⟩ : ∃ y0 : FramesV G, ∀ τ, y0.1 τ = Matrix.of fun a b => x (τ, a, b) :=
        ⟨⟨fun τ => Matrix.of fun a b => x (τ, a, b), fun τ => (hx τ).isUnit⟩, fun _ => rfl⟩
      have hy : fnOfV G s 1 P y0 = 0 := by rw [h]; rfl
      rw [fnOfV_one_apply] at hy
      simp only [hy0, Matrix.of_apply] at hy
      rcases mul_eq_zero.mp hy with h0 | h0
      · exact absurd h0 (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ))
      · exact mul_eq_zero_of_right _ h0
    · push_neg at hx
      obtain ⟨τ, hτ⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, zero_mul]
  simpa [detBlocks_ne_zero] using hz
end Formalism.L2.SG.Pf.ColDictValCPf
