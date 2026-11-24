-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.degenerateFactorBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:06.409366+00:00
-- url     : https://prove2.me/submissions/27635c2f-34f1-4b93-b883-fad326c5a1ca

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DeDegBound := by
  intro f s g T G₁ G₂ K₁ K₂ HH₁ HH₂ hg hT hG₁ hG₂ h₁ h₂ hK₁ hK₂ hk₁ hk₂ h9
  have hH₁ : 0 ≤ HH₁ := hG₁.trans h₁
  have hH₂ : 0 ≤ HH₂ := hG₂.trans h₂
  have hq : (2 / g) ^ ((s - 2) * f) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [div_le_one (by linarith)]; exact hg)
  have hTi : T⁻¹ ≤ 1 := by have := inv_anti₀ one_pos hT; simpa using this
  have hTf : T⁻¹ ^ f ≤ 1 := pow_le_one₀ (by positivity) hTi
  have hY0 : 0 ≤ Real.sqrt (G₁ * G₂) * K₁ * K₂ := by positivity
  have hY : Real.sqrt (G₁ * G₂) * K₁ * K₂ ≤ (HH₁ * HH₂) ^ 3 := by
    have hsq : (Real.sqrt (G₁ * G₂) * K₁ * K₂) ^ 2 ≤ ((HH₁ * HH₂) ^ 3) ^ 2 := by
      have e : (Real.sqrt (G₁ * G₂) * K₁ * K₂) ^ 2 = (G₁ * G₂) * (K₁ ^ 2 * K₂ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hG₁ hG₂)]; ring
      rw [e]
      calc (G₁ * G₂) * (K₁ ^ 2 * K₂ ^ 2)
            ≤ (HH₁ * HH₂) * ((9 ^ f * HH₁ ^ 3) * (9 ^ f * HH₂ ^ 3)) :=
            mul_le_mul (mul_le_mul h₁ h₂ hG₂ hH₁) (mul_le_mul hk₁ hk₂ (by positivity) (by positivity))
              (by positivity) (by positivity)
        _ = (9 ^ f) ^ 2 * (HH₁ * HH₂) ^ 4 := by ring
        _ ≤ (HH₁ * HH₂) ^ 2 * (HH₁ * HH₂) ^ 4 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h9 2) (by positivity)
        _ = ((HH₁ * HH₂) ^ 3) ^ 2 := by ring
    calc Real.sqrt (G₁ * G₂) * K₁ * K₂ = Real.sqrt ((Real.sqrt (G₁ * G₂) * K₁ * K₂) ^ 2) :=
          (Real.sqrt_sq hY0).symm
      _ ≤ Real.sqrt (((HH₁ * HH₂) ^ 3) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = (HH₁ * HH₂) ^ 3 := Real.sqrt_sq (by positivity)
  calc (2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂
        = ((2 / g) ^ ((s - 2) * f) * T⁻¹ ^ f) * (Real.sqrt (G₁ * G₂) * K₁ * K₂) := by ring
    _ ≤ (1 * 1) * (HH₁ * HH₂) ^ 3 :=
        mul_le_mul (mul_le_mul hq hTf (by positivity) zero_le_one) hY hY0 (by norm_num)
    _ = (HH₁ * HH₂) ^ 3 := by ring
end Formalism.HermitianLatticeCounting.P
