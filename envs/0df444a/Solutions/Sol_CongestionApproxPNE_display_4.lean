-- Prove2me | solution 1 for CongestionApproxPNE.display_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:04:43.290779+00:00
-- url     : https://prove2.me/submissions/a686d441-d242-4e76-b574-75450f607697

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

open CongestionApproxPNE in
theorem solution (d : ℕ) (hd : 4 ≤ d) :
    2 * Real.sqrt d / Real.log d ≤
      1 + (nChoice d : ℝ) * betaChoice d * (1 + wChoice d) ^ d := by
  have hD : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hDpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hDpos
  have hs2 : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hDpos.le
  have hwdef : wChoice d = Real.log (d : ℝ) / (2 * (d : ℝ)) := rfl
  have hw : 0 < wChoice d := by rw [hwdef]; exact div_pos hlog (by linarith)
  have hk0 : (0 : ℝ) ≤ (kd d : ℝ) := Nat.cast_nonneg _
  have hab : 1 / (2 * ((kd d : ℝ) + 1)) + (kd d : ℝ) / (2 * ((kd d : ℝ) + 1)) = 1 / 2 := by
    rw [← add_div, div_eq_div_iff (by positivity) (by norm_num)]
    ring
  unfold betaChoice nChoice
  obtain ⟨Da, hDa⟩ : ∃ Da : ℝ, Da = (d : ℝ) ^ (1 / (2 * ((kd d : ℝ) + 1))) := ⟨_, rfl⟩
  obtain ⟨Db, hDb⟩ : ∃ Db : ℝ, Db = (d : ℝ) ^ ((kd d : ℝ) / (2 * ((kd d : ℝ) + 1))) := ⟨_, rfl⟩
  have hDa0 : 0 < Da := by rw [hDa]; exact Real.rpow_pos_of_pos hDpos _
  have hDb1 : 1 ≤ Db := by
    rw [hDb]; exact Real.one_le_rpow (by linarith) (div_nonneg hk0 (by positivity))
  have hDb0 : 0 < Db := by linarith
  have hprod : Da * Db = Real.sqrt (d : ℝ) := by
    rw [hDa, hDb, ← Real.rpow_add hDpos, hab, Real.sqrt_eq_rpow]
  rw [← hDa, ← hDb]
  obtain ⟨w, hwe⟩ : ∃ w : ℝ, w = wChoice d := ⟨_, rfl⟩
  rw [← hwe]
  rw [← hwe] at hw hwdef
  have hP : 0 < (1 + w) ^ d := pow_pos (by linarith) d
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 / (Da * w) := ⟨_, rfl⟩
  rw [← hA]
  have hn : A < (⌊A⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one A
  obtain ⟨n, hnd⟩ : ∃ n : ℕ, n = ⌊A⌋₊ := ⟨_, rfl⟩
  rw [← hnd]
  rw [← hnd] at hn
  have hAB : A / Db = 2 * Real.sqrt (d : ℝ) / Real.log (d : ℝ) := by
    have e1 : A / Db = 1 / (Da * Db * w) := by rw [hA, div_div, mul_right_comm]
    rw [e1, hprod, hwdef,
      div_eq_div_iff (mul_pos hs (div_pos hlog (by linarith))).ne' hlog.ne',
      show (2 : ℝ) * Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ) * (Real.log (d : ℝ) / (2 * (d : ℝ))))
        = (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) * Real.log (d : ℝ) / (d : ℝ) by ring,
      hs2, mul_div_cancel_left₀ _ hDpos.ne', one_mul]
  have hsimp : (n : ℝ) * (1 / (Db * (1 + w) ^ d)) * (1 + w) ^ d = (n : ℝ) / Db := by
    have hDbne : Db ≠ 0 := hDb0.ne'
    have hPne : (1 + w) ^ d ≠ 0 := hP.ne'
    field_simp
    try ring
  rw [← hAB, hsimp, div_le_iff₀ hDb0, add_mul, one_mul, div_mul_cancel₀ _ hDb0.ne']
  linarith
