-- Prove2me | solution 1 for Erdos3.bloom_sisask_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:35:41.300495+00:00
-- url     : https://prove2.me/submissions/f3f63541-1bad-4e97-9651-f8e7dc405ec0

import Definitions.Def_Erdos142Basic
import Theorems.Thm_Erdos142_kelley_meka
import Mathlib

namespace Erdos3Aux
open Erdos142

/-- From the Kelley--Meka bound `r_3(N) ≤ N exp(-c₀ (log N)^(1/12))` we get
`r_3(N) ≤ N / (log N)^2` for large `N`. -/
theorem km_to_bs :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r 3 N : ℝ) ≤ (N : ℝ) / (Real.log N) ^ (1 + c) := by
  obtain ⟨c₀, hc₀, hkm⟩ := kelley_meka
  refine ⟨1, one_pos, ?_⟩
  have hu : Filter.Tendsto (fun N : ℕ => (Real.log N) ^ ((1 : ℝ) / 12)) Filter.atTop
      Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hx : Filter.Tendsto (fun N : ℕ => c₀ * (Real.log N) ^ ((1 : ℝ) / 12)) Filter.atTop
      Filter.atTop := hu.const_mul_atTop hc₀
  have hlim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 24
  have hev : ∀ᶠ x : ℝ in Filter.atTop, x ^ 24 * Real.exp (-x) < c₀ ^ 24 :=
    hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hkm, hx.eventually hev, Filter.eventually_gt_atTop 1] with N h1 h2 h3
  have hN : (1 : ℝ) < N := by exact_mod_cast h3
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  set L := Real.log N with hLdef
  set u := L ^ ((1 : ℝ) / 12) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hL _
  have hu24 : u ^ 24 = L ^ 2 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    rw [show (1 : ℝ) / 12 * ((24 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2' : u ^ 24 * Real.exp (-(c₀ * u)) < 1 := by
    have : c₀ ^ 24 * (u ^ 24 * Real.exp (-(c₀ * u))) < c₀ ^ 24 * 1 := by
      calc c₀ ^ 24 * (u ^ 24 * Real.exp (-(c₀ * u)))
          = (c₀ * u) ^ 24 * Real.exp (-(c₀ * u)) := by ring
        _ < c₀ ^ 24 := h2
        _ = c₀ ^ 24 * 1 := by ring
    exact lt_of_mul_lt_mul_left this (by positivity)
  rw [hu24] at h2'
  have hpow : L ^ (1 + (1 : ℝ)) = L ^ 2 := by
    rw [show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow]
  refine h1.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have : -c₀ * u = -(c₀ * u) := by ring
  rw [this]
  nlinarith [mul_pos hN0 (sub_pos.mpr h2')]

end Erdos3Aux

open Erdos142

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r 3 N : ℝ) ≤ (N : ℝ) / (Real.log N) ^ (1 + c) :=
  Erdos3Aux.km_to_bs
