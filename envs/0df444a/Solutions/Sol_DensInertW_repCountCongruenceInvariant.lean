-- Prove2me | solution 1 for DensInertW.repCountCongruenceInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:08.48683+00:00
-- url     : https://prove2.me/submissions/b9c50c67-3111-4028-9242-1e99d5d84bed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant
import Theorems.Thm_DensInertW_cg_comb_comb
import Theorems.Thm_DensInertW_cg_comb_one
import Theorems.Thm_DensInertW_cg_mem
import Theorems.Thm_DensInertW_cg_indep
import Theorems.Thm_DensInertW_cg_gram
import Theorems.Thm_DensInertW_cg_map_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open DensInertW
namespace DensInertW
theorem _root_.solution : Congr := by
  intro K L _ _ _ _ _ _ n M W m B P hP
  have hdet : P.det ≠ 0 := hP.ne_zero
  have hq1 : 0 < Fintype.card K := Fintype.card_pos
  have hmap1 : (1 : Matrix (Fin m) (Fin m) L).map (fun y => y ^ Fintype.card K) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, zero_pow hq1.ne']
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPinv' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hinj : Function.Injective (fun X : Fin m → Fin n → L => cgComb P X) := fun X Y h => by
    have h2 := congrArg (cgComb P⁻¹) h
    simpa [cg_comb_comb, hPinv', cg_comb_one] using h2
  have e : (P.map (fun y => y ^ Fintype.card K)).transpose *
      (P⁻¹.map (fun y => y ^ Fintype.card K)).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← cg_map_mul K L, hPinv', hmap1, Matrix.transpose_one]
  have e2 : P⁻¹ * (P * B * (P.map (fun y => y ^ Fintype.card K)).transpose) *
      (P⁻¹.map (fun y => y ^ Fintype.card K)).transpose = B := by
    simp only [Matrix.mul_assoc, e, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hPinv', Matrix.one_mul]
  unfold cntT
  convert Set.ncard_image_of_injective _ hinj using 2
  ext Y
  constructor
  · rintro ⟨hW, hI, hG⟩
    refine ⟨cgComb P⁻¹ Y, ⟨cg_mem _ _ _ hW,
      cg_indep _ _ (Matrix.isUnit_nonsing_inv_det P hP).ne_zero hI, fun i j => ?_⟩, ?_⟩
    · rw [cg_gram K L M P⁻¹ _ Y hG, e2]
    · show cgComb P (cgComb P⁻¹ Y) = Y
      rw [cg_comb_comb, hPinv, cg_comb_one]
  · rintro ⟨X, ⟨hW, hI, hG⟩, rfl⟩
    exact ⟨cg_mem _ _ _ hW, cg_indep _ _ hdet hI, fun i j => cg_gram K L M P B X hG i j⟩
end DensInertW
