-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.realB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:21.044521+00:00
-- url     : https://prove2.me/submissions/63111be7-d90b-4bf5-89d8-e99a1b993a77

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsTorsion
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K}
namespace Formalism.ELL.FormalGroupPointsTorsion
theorem _root_.solution {t1 t2 X1 X2 X3 V L : ℝ} (ht1 : 0 < t1) (ht2 : 0 < t2)
    (h1 : t1 ^ 2 * X1 = 1) (h2 : t2 ^ 2 * X2 = 1)
    (hX1 : 1 < X1) (hX2 : 1 < X2) (hX3 : 1 < X3) (hV0 : 0 ≤ V) (hV : V ^ 2 = X1 * X2 * X3)
    (hL0 : 0 ≤ L) (hL : L ^ 2 ≤ max (max X1 X2) X3) :
    1 < max t1 t2 * V ∧ L < max t1 t2 * V := by
  set S := max t1 t2
  have hS1 : t1 ≤ S := le_max_left _ _
  have hS2 : t2 ≤ S := le_max_right _ _
  have hSV0 : 0 ≤ S * V := mul_nonneg (ht1.le.trans hS1) hV0
  have hA : X2 * X3 ≤ (S * V) ^ 2 := by
    have : t1 ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ ht1.le hS1 2
    have : X2 * X3 = t1 ^ 2 * V ^ 2 := by rw [hV]; linear_combination (-(X2 * X3)) * h1
    rw [this, mul_pow]; exact mul_le_mul_of_nonneg_right (by assumption) (sq_nonneg _)
  have hB : X1 * X3 ≤ (S * V) ^ 2 := by
    have : t2 ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ ht2.le hS2 2
    have : X1 * X3 = t2 ^ 2 * V ^ 2 := by rw [hV]; linear_combination (-(X1 * X3)) * h2
    rw [this, mul_pow]; exact mul_le_mul_of_nonneg_right (by assumption) (sq_nonneg _)
  constructor
  · have : 1 < (S * V) ^ 2 := by nlinarith
    by_contra hc; push_neg at hc
    nlinarith
  · have : L ^ 2 < (S * V) ^ 2 := by
      refine hL.trans_lt ?_
      refine max_lt (max_lt ?_ ?_) ?_ <;> nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hSV0 this
end Formalism.ELL.FormalGroupPointsTorsion
