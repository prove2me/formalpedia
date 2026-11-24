-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.nondegenerateFactorBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:44.169395+00:00
-- url     : https://prove2.me/submissions/7ca6155f-e2fa-4a6d-99d4-0cff641943ff

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
theorem _root_.solution : DeNonDegBound := by
  intro f s g G₁ G₂ HH₁ HH₂ hg hG₁ hG₂ h₁ h₂ hH₁ hH₂
  have hH : 1 ≤ HH₁ * HH₂ := one_le_mul_of_one_le_of_one_le hH₁ hH₂
  have hq : (2 / g) ^ ((s - 1) * f) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [div_le_one (by linarith)]; exact hg)
  have hsq : Real.sqrt (G₁ * G₂) ≤ HH₁ * HH₂ := by
    calc Real.sqrt (G₁ * G₂) ≤ Real.sqrt (HH₁ * HH₂) :=
          Real.sqrt_le_sqrt (mul_le_mul h₁ h₂ hG₂ (by linarith))
      _ ≤ Real.sqrt ((HH₁ * HH₂) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = HH₁ * HH₂ := Real.sqrt_sq (by linarith)
  have h1 : (2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) ≤ HH₁ * HH₂ := by
    calc (2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) ≤ 1 * (HH₁ * HH₂) :=
          mul_le_mul hq hsq (Real.sqrt_nonneg _) zero_le_one
      _ = HH₁ * HH₂ := one_mul _
  refine ⟨h1, h1.trans ?_⟩
  calc HH₁ * HH₂ = (HH₁ * HH₂) ^ 1 := (pow_one _).symm
    _ ≤ (HH₁ * HH₂) ^ 3 := pow_le_pow_right₀ hH (by norm_num)
end Formalism.HermitianLatticeCounting.P
