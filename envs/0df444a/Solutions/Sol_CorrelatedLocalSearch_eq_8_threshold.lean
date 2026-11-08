-- Prove2me | solution 1 for CorrelatedLocalSearch.eq_8_threshold
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:09:39.526987+00:00
-- url     : https://prove2.me/submissions/efdcf001-2ec6-4a3e-81e1-8961adf46140

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar

set_option autoImplicit false

namespace Aux_Q01_eq_8_threshold

theorem key1 (sa sb : ℝ) (h1 : 0 < sa) (h2 : 0 < sb) :
    sa ^ 2 * (2 * (sa * sb))⁻¹ = sa / sb / 2 := by
  have h1' : sa ≠ 0 := h1.ne'
  have h2' : sb ≠ 0 := h2.ne'
  field_simp <;> ring

theorem key2 (sa sb : ℝ) (h1 : 0 < sa) (h2 : 0 < sb) :
    sb ^ 2 * (2 * (sa * sb))⁻¹ = 1 / (2 * (sa / sb)) := by
  have h1' : sa ≠ 0 := h1.ne'
  have h2' : sb ≠ 0 := h2.ne'
  field_simp <;> ring

end Aux_Q01_eq_8_threshold

open CorrelatedLocalSearch in
theorem solution (k r : ℕ) (hk : k < 2 * r) (hr : r < k) :
    1 < lam k r ∧ 0 < sStar k r ∧ sStar k r < 1 ∧
      (r : ℝ) * (k : ℝ) ^ (-sStar k r) = lam k r / 2 ∧
      ((k : ℝ) - r) * (k : ℝ) ^ (-sStar k r) = 1 / (2 * lam k r) := by
  have hr1 : (1 : ℝ) ≤ r := by
    have : 1 ≤ r := by omega
    exact_mod_cast this
  have hb1 : (1 : ℝ) ≤ (k : ℝ) - r := by
    have : r + 1 ≤ k := hr
    have : ((r : ℝ) + 1 ≤ k) := by exact_mod_cast this
    linarith
  have hab : (k : ℝ) - r < r := by
    have : ((k : ℝ) < 2 * r) := by exact_mod_cast hk
    linarith
  have ha : (0 : ℝ) < r := by linarith
  have hb : (0 : ℝ) < (k : ℝ) - r := by linarith
  have hk1 : (1 : ℝ) < k := by linarith
  have hsa : 0 < Real.sqrt r := Real.sqrt_pos.mpr ha
  have hsb : 0 < Real.sqrt ((k : ℝ) - r) := Real.sqrt_pos.mpr hb
  have hsa2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt ha.le
  have hsb2 : Real.sqrt ((k : ℝ) - r) ^ 2 = (k : ℝ) - r := Real.sq_sqrt hb.le
  have hlam : lam k r = Real.sqrt r / Real.sqrt ((k : ℝ) - r) := by
    unfold lam
    exact Real.sqrt_div ha.le _
  have hq : Real.sqrt ((r : ℝ) * ((k : ℝ) - r)) = Real.sqrt r * Real.sqrt ((k : ℝ) - r) :=
    Real.sqrt_mul ha.le _
  have hlt : Real.sqrt ((k : ℝ) - r) < Real.sqrt r := Real.sqrt_lt_sqrt hb.le hab
  have hprod1 : (1 : ℝ) ≤ (r : ℝ) * ((k : ℝ) - r) := by nlinarith
  have hq1 : 1 ≤ Real.sqrt ((r : ℝ) * ((k : ℝ) - r)) := Real.one_le_sqrt.mpr hprod1
  have hqpos : 0 < 2 * Real.sqrt ((r : ℝ) * ((k : ℝ) - r)) := by linarith
  have hpow : (k : ℝ) ^ (-sStar k r) = (2 * (Real.sqrt r * Real.sqrt ((k : ℝ) - r)))⁻¹ := by
    unfold sStar
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ k), Real.rpow_logb (by linarith : (0 : ℝ) < k) hk1.ne' hqpos, hq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hlam, one_lt_div hsb]
    exact hlt
  · unfold sStar
    exact Real.logb_pos hk1 (by linarith)
  · unfold sStar
    rw [Real.logb_lt_iff_lt_rpow hk1 hqpos, Real.rpow_one]
    have h2r : (0 : ℝ) < 2 * r - k := by linarith
    have hsq : Real.sqrt ((r : ℝ) * ((k : ℝ) - r)) < (k : ℝ) / 2 := by
      rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < (k : ℝ) / 2)]
      nlinarith [mul_pos h2r h2r]
    linarith
  · rw [hpow, hlam]
    calc (r : ℝ) * (2 * (Real.sqrt r * Real.sqrt ((k : ℝ) - r)))⁻¹
        = Real.sqrt r ^ 2 * (2 * (Real.sqrt r * Real.sqrt ((k : ℝ) - r)))⁻¹ := by rw [hsa2]
      _ = Real.sqrt r / Real.sqrt ((k : ℝ) - r) / 2 := Aux_Q01_eq_8_threshold.key1 _ _ hsa hsb
  · rw [hpow, hlam]
    calc ((k : ℝ) - r) * (2 * (Real.sqrt r * Real.sqrt ((k : ℝ) - r)))⁻¹
        = Real.sqrt ((k : ℝ) - r) ^ 2 * (2 * (Real.sqrt r * Real.sqrt ((k : ℝ) - r)))⁻¹ := by
          rw [hsb2]
      _ = 1 / (2 * (Real.sqrt r / Real.sqrt ((k : ℝ) - r))) :=
          Aux_Q01_eq_8_threshold.key2 _ _ hsa hsb
