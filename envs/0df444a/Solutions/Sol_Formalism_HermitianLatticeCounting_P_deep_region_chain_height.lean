-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.deep_region_chain_height
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:06.199699+00:00
-- url     : https://prove2.me/submissions/aa825d6d-07c2-410c-9e90-d693b3fccbf4

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DeepChainY := by
  intro C n q f Y τ₁ τs θ Kxx Bs D volG volK hC hq hY hτ hττ hD hvK hvG hθ0 hθ hK hB hvol
  have hY0 : 0 < Y := by linarith
  have hq0 : q ≠ 0 := by omega
  set m : ℕ := n ^ 2 * f with hm
  have hmr : (m:ℝ) = (n:ℝ) ^ 2 * f := by rw [hm]; push_cast; ring
  have hP : 2 * P0 n q f = q * (16 * m) := by rw [hm]; unfold P0; ring
  have e4 : 4 * n ^ 2 * f = 4 * m := by rw [hm]; ring
  have e12 : 12 * n ^ 2 * f = 12 * m := by rw [hm]; ring
  rw [hP] at hK
  rw [e4] at hB
  rw [e12]
  have eC : C * (n:ℝ) ^ 2 * f = C * m := by rw [hmr]; ring
  rw [eC] at hB hvol
  have hT : θ ^ (q * (16 * m)) ≤ Y ^ (16 * q * C * m) * (2 * τ₁) ^ (16 * m) := by
    calc θ ^ (q * (16 * m)) ≤ (Y ^ C * (2 * τ₁) ^ ((1:ℝ) / q)) ^ (q * (16 * m)) :=
          pow_le_pow_left₀ hθ0 hθ _
      _ = (Y ^ C) ^ (q * (16 * m)) * ((2 * τ₁) ^ ((1:ℝ) / q)) ^ (q * (16 * m)) := mul_pow _ _ _
      _ = _ := by
        congr 1
        · rw [← Real.rpow_mul_natCast hY0.le]
          congr 1; push_cast; ring
        · rw [pow_mul, one_div, Real.rpow_inv_natCast_pow (by linarith) hq0]
  set a := Y ^ (C * m) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hY0 _
  have hT0 : 0 ≤ θ ^ (q * (16 * m)) := pow_nonneg hθ0 _
  have hi0 : 0 < (1 / τ₁) ^ (4 * m) := by positivity
  have s1 : volG * Kxx ≤ θ ^ (q * (16 * m)) * a * (1 / τ₁) ^ (4 * m) * D * a := by
    calc volG * Kxx ≤ volG * (θ ^ (q * (16 * m)) * (a * (1 / τ₁) ^ (4 * m) * D / volK)) := by
          apply mul_le_mul_of_nonneg_left _ hvG
          exact hK.trans (mul_le_mul_of_nonneg_left hB hT0)
      _ = θ ^ (q * (16 * m)) * a * (1 / τ₁) ^ (4 * m) * D * (volG / volK) := by ring
      _ ≤ _ := by gcongr
  have s2 : (2 * τ₁) ^ (16 * m) * (1 / τ₁) ^ (4 * m) = 2 ^ (16 * m) * τ₁ ^ (12 * m) := by
    have : 16 * m = 12 * m + 4 * m := by ring
    rw [mul_pow, one_div, inv_pow]
    conv_lhs => rw [this, pow_add τ₁]
    have h4 : τ₁ ^ (4 * m) ≠ 0 := by positivity
    rw [← this]
    field_simp
  have s3 : (2:ℝ) ^ (16 * m) * τ₁ ^ (12 * m) ≤ Y ^ (16 * m) * τs ^ (12 * m) := by
    gcongr
  have eY : Y ^ ((16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f)
      = Y ^ (16 * q * C * m) * a * a * Y ^ (16 * m) := by
    rw [ha, ← Real.rpow_natCast Y (16 * m), ← Real.rpow_add hY0, ← Real.rpow_add hY0,
      ← Real.rpow_add hY0]
    congr 1; push_cast; rw [hmr]; ring
  rw [eY]
  have hb0 : 0 < Y ^ (16 * q * C * m) := Real.rpow_pos_of_pos hY0 _
  calc volG * Kxx ≤ θ ^ (q * (16 * m)) * a * (1 / τ₁) ^ (4 * m) * D * a := s1
    _ ≤ (Y ^ (16 * q * C * m) * (2 * τ₁) ^ (16 * m)) * a * (1 / τ₁) ^ (4 * m) * D * a := by gcongr
    _ = D * (Y ^ (16 * q * C * m) * a * a) * ((2 * τ₁) ^ (16 * m) * (1 / τ₁) ^ (4 * m)) := by ring
    _ ≤ D * (Y ^ (16 * q * C * m) * a * a) * (Y ^ (16 * m) * τs ^ (12 * m)) := by
        rw [s2]; gcongr
    _ = _ := by ring
end Formalism.HermitianLatticeCounting.P
