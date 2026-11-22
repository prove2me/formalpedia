-- Prove2me | solution 1 for GJKKL.Numerics.final_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:07.387829+00:00
-- url     : https://prove2.me/submissions/1c955010-a142-4abd-b73e-4f84606ef454

module
public import Definitions.Def_GJKKL_Numerics_Falling
public import Definitions.Def_GJKKL_Numerics_Final
public import Theorems.Thm_GJKKL_Numerics_count_factor_ge


set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real
namespace GJKKL.Numerics
theorem _root_.solution {a μ η η4 d P : ℝ} {k1 m : ℕ} (ha : 0 < a) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hη0 : 0 ≤ η) (hημ : η ≤ μ / 2) (hη4 : η ≤ η4) (hη41 : η4 ≤ 1) (hd : 0 ≤ d)
    (hm1 : 1 ≤ m) (hm : (m : ℝ) ≤ (1 - μ) * a) (haμ : 4 ≤ a * μ) (hP : 1 / 2 ≤ P) :
    ((1 - η4) * d / exp k1) ^ m ≤
      P * ((1 - η) * d) ^ m *
        (a ^ m * (∏ i ∈ range m, (1 - (i : ℝ) / a)) ^ (k1 + 1) / m.factorial) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hma : (m : ℝ) ≤ a := by nlinarith
  have hcf := count_factor_ge a ha m k1 hma
  have hE : 0 < exp (k1 : ℝ) := exp_pos _
  set X := (1 - η) * d / exp k1 with hX
  set Y := (1 - η4) * d / exp k1 with hY
  have hY0 : 0 ≤ Y := by rw [hY]; exact div_nonneg (mul_nonneg (by linarith) hd) hE.le
  have hYX : Y ≤ X := by
    rw [hY, hX]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hd) hE.le
  have hX0 : 0 ≤ X := hY0.trans hYX
  -- the right-hand side is at least `P X^m (a/m)^m`
  have hexp : exp (-((k1 : ℝ) * m)) = (exp k1)⁻¹ ^ m := by
    rw [← exp_neg, ← exp_nat_mul]; ring_nf
  have hR : P * X ^ m * (a / m) ^ m ≤ P * ((1 - η) * d) ^ m *
      (a ^ m * (∏ i ∈ range m, (1 - (i : ℝ) / a)) ^ (k1 + 1) / m.factorial) := by
    have hP0 : 0 ≤ P := by linarith
    have hpow : 0 ≤ ((1 - η) * d) ^ m := pow_nonneg (mul_nonneg (by linarith) hd) m
    calc P * X ^ m * (a / m) ^ m = P * ((1 - η) * d) ^ m * (exp (-((k1 : ℝ) * m)) * (a / m) ^ m) := by
          rw [hexp, hX, div_eq_mul_inv, mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcf (mul_nonneg hP0 hpow)
  refine le_trans ?_ hR
  by_cases h2 : 2 ≤ a / m
  · -- `(a/m)^m ≥ 2`
    have hpow2 : 2 ≤ (a / m) ^ m := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm1
        _ ≤ (a / m) ^ m := pow_le_pow_left₀ (by norm_num) h2 m
    have hYm : Y ^ m ≤ X ^ m := pow_le_pow_left₀ hY0 hYX m
    have hXm : 0 ≤ X ^ m := pow_nonneg hX0 m
    have hPA : 1 ≤ P * (a / m) ^ m := by
      nlinarith [mul_nonneg (show 0 ≤ P - 1 / 2 by linarith) (show 0 ≤ (a / m) ^ m - 2 by linarith)]
    calc Y ^ m ≤ X ^ m * 1 := by rw [mul_one]; exact hYm
      _ ≤ X ^ m * (P * (a / m) ^ m) := mul_le_mul_of_nonneg_left hPA hXm
      _ = P * X ^ m * (a / m) ^ m := by ring
  · -- `m > a/2`: the ratio `(1 - η)/(1 - μ) ≥ 1 + μ/2` absorbs the factor `2`
    push_neg at h2
    have hma2 : a < 2 * m := by rwa [div_lt_iff₀ hm0] at h2
    set Z := d / exp k1 with hZ
    have hZ0 : 0 ≤ Z := div_nonneg hd hE.le
    have hXZ : X = (1 - η) * Z := by rw [hX, hZ]; ring
    have hYZ : Y ≤ Z := by rw [hY, hZ]; exact div_le_div_of_nonneg_right (by nlinarith) hE.le
    have ham : 1 / (1 - μ) ≤ a / m := by
      rw [div_le_div_iff₀ (by linarith) hm0]; linarith
    have hratio : 1 + μ / 2 ≤ (1 - η) * (a / m) := by
      calc 1 + μ / 2 ≤ (1 - η) * (1 / (1 - μ)) := by
            rw [mul_one_div, le_div_iff₀ (by linarith)]; nlinarith
        _ ≤ (1 - η) * (a / m) := mul_le_mul_of_nonneg_left ham (by linarith)
    have hbern : 1 + (m : ℝ) * (μ / 2) ≤ (1 + μ / 2) ^ m :=
      one_add_mul_le_pow (by linarith) m
    have h2' : 2 ≤ 1 + (m : ℝ) * (μ / 2) := by nlinarith
    have hgrow : 2 ≤ ((1 - η) * (a / m)) ^ m :=
      h2'.trans (hbern.trans (pow_le_pow_left₀ (by linarith) hratio m))
    have hXam : X ^ m * (a / m) ^ m = ((1 - η) * (a / m)) ^ m * Z ^ m := by
      rw [hXZ, ← mul_pow, ← mul_pow]; ring_nf
    have hYm : Y ^ m ≤ Z ^ m := pow_le_pow_left₀ hY0 hYZ m
    have hZm : 0 ≤ Z ^ m := pow_nonneg hZ0 m
    rw [mul_assoc, hXam]
    have hPG : 1 ≤ P * ((1 - η) * (a / m)) ^ m := by
      nlinarith [mul_nonneg (show 0 ≤ P - 1 / 2 by linarith)
        (show 0 ≤ ((1 - η) * (a / m)) ^ m - 2 by linarith)]
    calc Y ^ m ≤ Z ^ m * 1 := by rw [mul_one]; exact hYm
      _ ≤ Z ^ m * (P * ((1 - η) * (a / m)) ^ m) := mul_le_mul_of_nonneg_left hPG hZm
      _ = P * (((1 - η) * (a / m)) ^ m * Z ^ m) := by ring
end GJKKL.Numerics
