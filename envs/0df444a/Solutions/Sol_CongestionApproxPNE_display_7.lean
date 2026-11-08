-- Prove2me | solution 1 for CongestionApproxPNE.display_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:53:42.583878+00:00
-- url     : https://prove2.me/submissions/2dab2978-907b-4719-ae24-581e7300e893

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

open CongestionApproxPNE in
theorem solution (d : ℕ) (hd : 4 ≤ d) :
    ((nChoice d : ℝ) * wChoice d) ^ kd d + betaChoice d * (1 + wChoice d) ^ d ≤
      2 * Real.log d / Real.sqrt d := by
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hlog2 := Real.log_two_gt_d9
  have hL4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hL : 4 / 3 < Real.log d := by
    have : Real.log 4 ≤ Real.log d := Real.log_le_log (by norm_num) hdR
    linarith
  set L := Real.log d with hLdef
  have hLpos : 0 < L := by linarith
  have hLL : 1 / 4 ≤ Real.log L := by
    have h := Real.one_sub_inv_le_log_of_pos hLpos
    have : L⁻¹ ≤ 3 / 4 := by rw [inv_le_comm₀ hLpos (by norm_num)]; linarith
    linarith
  have hLLpos : 0 < Real.log L := by linarith
  set k := kd d with hkdef
  have hk : L / (2 * Real.log L) ≤ (k : ℝ) := by
    rw [hkdef]; unfold kd; exact Nat.le_ceil _
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk
  set w := wChoice d with hwdef
  have hw : 0 < w := by rw [hwdef]; unfold wChoice; positivity
  set g : ℝ := 1 / (2 * ((k : ℝ) + 1)) with hg
  set f : ℝ := (k : ℝ) / (2 * ((k : ℝ) + 1)) with hf
  have hfg : f + g = 1 / 2 := by rw [hf, hg]; field_simp <;> ring
  have hdg : 0 < (d : ℝ) ^ g := Real.rpow_pos_of_pos hd0 g
  have hdf : 0 < (d : ℝ) ^ f := Real.rpow_pos_of_pos hd0 f
  -- term 1
  have ht1 : ((nChoice d : ℝ) * w) ^ k ≤ 1 / (d : ℝ) ^ f := by
    have hn : (nChoice d : ℝ) ≤ 1 / ((d : ℝ) ^ g * w) := by
      unfold nChoice; rw [← hg, ← hwdef]; exact Nat.floor_le (by positivity)
    have hnw : (nChoice d : ℝ) * w ≤ 1 / (d : ℝ) ^ g := by
      calc (nChoice d : ℝ) * w ≤ 1 / ((d : ℝ) ^ g * w) * w :=
            mul_le_mul_of_nonneg_right hn hw.le
        _ = 1 / (d : ℝ) ^ g := by field_simp
    have h0 : 0 ≤ (nChoice d : ℝ) * w := mul_nonneg (Nat.cast_nonneg _) hw.le
    calc ((nChoice d : ℝ) * w) ^ k ≤ (1 / (d : ℝ) ^ g) ^ k := pow_le_pow_left₀ h0 hnw k
      _ = 1 / (d : ℝ) ^ f := by
        rw [div_pow, one_pow, ← Real.rpow_natCast, ← Real.rpow_mul hd0.le]
        congr 2
        rw [hf, hg]; field_simp
  -- term 2
  have ht2 : betaChoice d * (1 + w) ^ d = 1 / (d : ℝ) ^ f := by
    unfold betaChoice
    rw [← hkdef, ← hwdef, ← hf]
    have : 0 < (1 + w) ^ d := pow_pos (by linarith) d
    field_simp
  -- exponent bound
  have hgle : g ≤ Real.log L / L := by
    rw [hg, div_le_div_iff₀ (by positivity) hLpos]
    have : L ≤ 2 * Real.log L * k := by
      rw [div_le_iff₀ (by positivity)] at hk; linarith
    nlinarith
  have hdgL : (d : ℝ) ^ g ≤ L := by
    calc (d : ℝ) ^ g ≤ (d : ℝ) ^ (Real.log L / L) :=
          Real.rpow_le_rpow_of_exponent_le hd1 hgle
      _ = L := by
        rw [Real.rpow_def_of_pos hd0, ← hLdef]
        rw [show L * (Real.log L / L) = Real.log L by field_simp]
        exact Real.exp_log hLpos
  have hsq : Real.sqrt d = (d : ℝ) ^ f * (d : ℝ) ^ g := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hd0, hfg]
  rw [ht2, hsq]
  have hsum : ((nChoice d : ℝ) * w) ^ k + 1 / (d : ℝ) ^ f ≤ 2 / (d : ℝ) ^ f := by
    have : 2 / (d : ℝ) ^ f = 1 / (d : ℝ) ^ f + 1 / (d : ℝ) ^ f := by ring
    linarith
  refine hsum.trans ?_
  rw [div_le_div_iff₀ hdf (by positivity)]
  nlinarith
