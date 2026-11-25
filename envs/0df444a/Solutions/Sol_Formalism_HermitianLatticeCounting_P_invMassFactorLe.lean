-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.invMassFactorLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:35.223368+00:00
-- url     : https://prove2.me/submissions/ed741b78-90d8-41cf-8e71-af65bcf9a930

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_zetaSeries
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_zetaSeries_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_factorialPiWeight_pos
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_mul_factorialPiWeight

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
theorem _root_.solution : InvMk := by
  intro f k v Lv hv hk hL
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hv0 : 0 < v := by linarith
  have hz1 : 1 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR k := one_le_zetaSeries k (by omega)
  have hzle : Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR k ≤ 1.356 := zetaSeries_le k hk
  have hzf : 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR k ^ f := pow_pos (by linarith) f
  have hL0 : 0 < Lv k := lt_of_lt_of_le (inv_pos.mpr hzf) hL
  have hLi : (Lv k)⁻¹ ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR k ^ f := by
    have := inv_anti₀ (inv_pos.mpr hzf) hL
    rwa [inv_inv] at this
  have hW := one_le_mul_factorialPiWeight v hv k (by omega)
  have hWpos := factorialPiWeight_pos v hv0 k
  have hWi : (s5bA v k)⁻¹ ≤
      (Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) := by
    calc (s5bA v k)⁻¹ = (s5bA v k)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (s5bA v k)⁻¹ * ((Real.exp 1 * Real.pi / (k * v)) ^ k *
            Real.sqrt (k / (2 * Real.pi)) * s5bA v k) :=
          mul_le_mul_of_nonneg_left hW (inv_nonneg.mpr hWpos.le)
      _ = (Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) := by
          rw [mul_comm (s5bA v k)⁻¹, mul_assoc, mul_inv_cancel₀ hWpos.ne', mul_one]
  have hs1 : Real.sqrt (k / (2 * Real.pi)) * 1.356 ≤ k := by
    have h1 : (k:ℝ) / (2 * Real.pi) ≤ ((k:ℝ) / 2) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul hk3 Real.pi_gt_three.le (by norm_num) hk0.le]
    have h2 : Real.sqrt (k / (2 * Real.pi)) ≤ k / 2 := by
      calc Real.sqrt (k / (2 * Real.pi)) ≤ Real.sqrt (((k:ℝ) / 2) ^ 2) := Real.sqrt_le_sqrt h1
        _ = k / 2 := Real.sqrt_sq (by positivity)
    nlinarith [Real.sqrt_nonneg (k / (2 * Real.pi))]
  have hs2 : Real.sqrt ((2 * v) ^ f) ≤ (2 * v) ^ f := by
    have h1 : 1 ≤ (2 * v) ^ f := one_le_pow₀ (by linarith)
    calc Real.sqrt ((2 * v) ^ f) ≤ Real.sqrt (((2 * v) ^ f) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = (2 * v) ^ f := Real.sqrt_sq (by positivity)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ
  have e : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) = s5bA v k := rfl
  rw [e, mul_inv, mul_inv, inv_inv, ← inv_pow]
  calc (s5bA v k)⁻¹ ^ f * Real.sqrt ((2 * v) ^ f) * (Lv k)⁻¹
        ≤ ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi))) ^ f *
            (2 * v) ^ f * (1.356:ℝ) ^ f :=
        mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by positivity) hWi f) hs2 (by positivity)
          (by positivity)) (hLi.trans (pow_le_pow_left₀ (by linarith) hzle f)) (by positivity)
          (by positivity)
    _ = ((Real.exp 1 * Real.pi / (k * v)) ^ k) ^ f * (Real.sqrt (k / (2 * Real.pi)) * 1.356) ^ f *
          (2 * v) ^ f := by ring
    _ ≤ ((Real.exp 1 * Real.pi / (k * v)) ^ k) ^ f * (k:ℝ) ^ f * (2 * v) ^ f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hs1 f) (by positivity)) (by positivity)
    _ = (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (k * (2 * v)) ^ f := by rw [pow_mul]; ring
end Formalism.HermitianLatticeCounting.P
