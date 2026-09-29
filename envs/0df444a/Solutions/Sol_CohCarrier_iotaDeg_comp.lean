-- Prove2me | solution 1 for CohCarrier.iotaDeg_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2494c3b4-3016-5344-ba2e-64b9b81d6ad9

import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_iotaDeg_comp

set_option autoImplicit false
open scoped MatrixGroups
open CohCarrier

theorem solution {M₁ M₂ M₃ d₁ d₂ : ℕ} {H₁ : Subgroup (ZMod M₁)ˣ} {H₂ : Subgroup (ZMod M₂)ˣ}
    {H₃ : Subgroup (ZMod M₃)ˣ}
    [NeZero M₂] [NeZero M₃] [NeZero d₁] [NeZero d₂] [NeZero (d₁ * d₂)]
    (h₁₂ : LevelLE M₁ M₂ H₁ H₂ d₁) (h₂₃ : LevelLE M₂ M₃ H₂ H₃ d₂)
    (h₁₃ : LevelLE M₁ M₃ H₁ H₃ (d₁ * d₂)) (γ : ↥(GammaH M₃ H₃)) :
    iotaDeg M₁ M₃ H₁ H₃ (d₁ * d₂) h₁₃ γ
      = iotaDeg M₁ M₂ H₁ H₂ d₁ h₁₂ (iotaDeg M₂ M₃ H₂ H₃ d₂ h₂₃ γ) := by
  apply Subtype.ext
  show conjLowerMat (d₁ * d₂) (γ : SL(2, ℤ)) (h₁₃.dvd_entry γ)
    = conjLowerMat d₁ (conjLowerMat d₂ (γ : SL(2, ℤ)) (h₂₃.dvd_entry γ))
        (h₁₂.dvd_entry (iotaDeg M₂ M₃ H₂ H₃ d₂ h₂₃ γ))
  have hd₁ : (d₁ : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d₁)
  have hd₂ : (d₂ : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d₂)
  obtain ⟨k, hk⟩ := h₁₃.dvd_entry γ
  push_cast at hk
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [conjLowerMat, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
  · rfl
  · push_cast; ring
  · push_cast
    rw [hk, Int.mul_ediv_cancel_left _ (mul_ne_zero hd₁ hd₂),
      show (d₁ : ℤ) * d₂ * k = d₂ * (d₁ * k) from by ring,
      Int.mul_ediv_cancel_left _ hd₂, Int.mul_ediv_cancel_left _ hd₁]
  · rfl

#print axioms solution

end S_CohCarrier_iotaDeg_comp
end P2MW
export P2MW.S_CohCarrier_iotaDeg_comp (solution)
