-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.heightExponentAssembly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:26.705559+00:00
-- url     : https://prove2.me/submissions/e3ed653c-16c9-4c75-b77e-70fe4bb81817

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
private theorem eighty_one_pow_mul_four_mul_pow_le_six_mul_pow (m : ℕ) (hm : 1 ≤ m) :
    (81:ℝ) ^ m * ((4 * m : ℕ) : ℝ) ^ (4 * m) ≤ ((6 * m : ℕ) : ℝ) ^ (6 * m) := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  rw [pow_mul, pow_mul, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have h4 : (0:ℝ) ≤ (m:ℝ) ^ 4 := by positivity
  have h2 : (1:ℝ) ≤ (m:ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 h4]
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : HeightExponentAssembly := by
  intro s r f A cf De NT HH hs hf hA hcf hDe hNT hHH hNT2 hDe3
  have hHH0 : 0 < HH := by linarith
  have hDe0 : 0 < De := by linarith
  have hNT0 : 0 < NT := by linarith
  have hNTH : NT ≤ HH := by nlinarith
  have hDN : De * NT ≤ HH ^ 4 := by
    calc De * NT ≤ HH ^ 3 * HH := mul_le_mul hDe3 hNTH hNT0.le (by positivity)
      _ = HH ^ 4 := by ring
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hf1 : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have B1 : (De * NT) ^ (A * (s + cf)) ≤ HH ^ (4 * (A * (s + cf))) := by
    calc (De * NT) ^ (A * (s + cf)) ≤ (HH ^ 4) ^ (A * (s + cf)) :=
          Real.rpow_le_rpow (by positivity) hDN (by positivity)
      _ = HH ^ (4 * (A * (s + cf))) := by
          rw [← Real.rpow_natCast HH 4, ← Real.rpow_mul hHH0.le]; norm_num
  have B2 : De ^ (cf + 4) ≤ HH ^ (3 * (cf + 4)) := by
    calc De ^ (cf + 4) ≤ (HH ^ 3) ^ (cf + 4) := Real.rpow_le_rpow hDe0.le hDe3 (by positivity)
      _ = HH ^ (3 * (cf + 4)) := by
          rw [← Real.rpow_natCast HH 3, ← Real.rpow_mul hHH0.le]; norm_num
  have B3 : NT ^ (2 * r) * De ^ r * 9 ^ (s * f) * HH ^ (9 * s + 9 * s * r + 16 * r ^ 2) ≤
      HH ^ (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) * 9 ^ (s * f) := by
    have h1 : NT ^ (2 * r) ≤ HH ^ r := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hNT2 r
    have h2 : De ^ r ≤ HH ^ (3 * r) := by
      rw [pow_mul]; exact pow_le_pow_left₀ hDe0.le hDe3 r
    calc NT ^ (2 * r) * De ^ r * 9 ^ (s * f) * HH ^ (9 * s + 9 * s * r + 16 * r ^ 2)
          ≤ HH ^ r * HH ^ (3 * r) * 9 ^ (s * f) * HH ^ (9 * s + 9 * s * r + 16 * r ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul h1 h2 (by positivity) (by positivity)) (by positivity)) (by positivity)
      _ = HH ^ (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) * 9 ^ (s * f) := by ring
  have hm1 : 1 ≤ s * f := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have B45 : (9:ℝ) ^ (s * f) * 9 ^ (s * f) * ((4 * f * s).factorial : ℝ) ≤
      (6 * (s:ℝ) * f) ^ (6 * s * f) := by
    have h81 := eighty_one_pow_mul_four_mul_pow_le_six_mul_pow (s * f) hm1
    have hfac : ((4 * f * s).factorial : ℝ) ≤ ((4 * (s * f) : ℕ) : ℝ) ^ (4 * (s * f)) := by
      rw [show 4 * f * s = 4 * (s * f) by ring]; exact_mod_cast Nat.factorial_le_pow (4 * (s * f))
    have e6 : (6 * (s:ℝ) * f) ^ (6 * s * f) = ((6 * (s * f) : ℕ) : ℝ) ^ (6 * (s * f)) := by
      rw [show 6 * s * f = 6 * (s * f) by ring]; push_cast; try ring
    rw [e6]
    calc (9:ℝ) ^ (s * f) * 9 ^ (s * f) * ((4 * f * s).factorial : ℝ)
          ≤ 81 ^ (s * f) * ((4 * (s * f) : ℕ) : ℝ) ^ (4 * (s * f)) := by
          rw [← mul_pow, show (9:ℝ) * 9 = 81 by norm_num]
          exact mul_le_mul_of_nonneg_left hfac (by positivity)
      _ ≤ _ := h81
  have hEnat : (HH ^ (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) * 9 ^ (s * f)) ^ 2 =
      HH ^ (((2 * (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) : ℕ)) : ℝ) *
        ((9:ℝ) ^ (s * f) * 9 ^ (s * f)) := by
    rw [Real.rpow_natCast]; ring
  have hexp : 4 * (A * (s + cf)) + 3 * (cf + 4) +
      (((2 * (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) : ℕ)) : ℝ) ≤
      (4 * A + 60) * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + (4 * A + 60) * cf := by
    push_cast
    have hs0 : (0:ℝ) ≤ s := by linarith
    nlinarith [mul_nonneg (mul_nonneg hA hr0) hs0, mul_nonneg hA hs0, mul_nonneg hA (mul_nonneg hr0 hr0),
      mul_nonneg hA hr0, mul_nonneg hr0 hs0, mul_nonneg hr0 hr0, mul_nonneg hA hcf]
  calc _ ≤ HH ^ (4 * (A * (s + cf))) * HH ^ (3 * (cf + 4)) *
        (HH ^ (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) * 9 ^ (s * f)) ^ 2 *
        ((4 * f * s).factorial : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul B1 B2 (by positivity) (by positivity))
          (pow_le_pow_left₀ (by positivity) B3 2) (by positivity) (by positivity)) (by positivity)
    _ = HH ^ (4 * (A * (s + cf)) + 3 * (cf + 4) +
          (((2 * (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) : ℕ)) : ℝ)) *
          ((9:ℝ) ^ (s * f) * 9 ^ (s * f) * ((4 * f * s).factorial : ℝ)) := by
        rw [hEnat, Real.rpow_add hHH0, Real.rpow_add hHH0]; ring
    _ ≤ HH ^ ((4 * A + 60) * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + (4 * A + 60) * cf) *
          (6 * (s:ℝ) * f) ^ (6 * s * f) :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le hHH hexp) B45 (by positivity) (by positivity)
end Formalism.HermitianLatticeCounting.P
