-- Prove2me | solution 1 for BinPacking.FirstFit.ratio_limit_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:40:50.619397+00:00
-- url     : https://prove2.me/submissions/6b5d518c-500a-4750-85d0-df636d58d833
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model
import Theorems.Thm_BinPacking_FirstFit_ff_bf_le_seventeen_tenths
import Theorems.Thm_BinPacking_FirstFit_ff_eq_bf_gt_seventeen_tenths_sub_eight

set_option autoImplicit false

namespace BinPacking.FirstFit

open Filter Topology

/-- Generic squeeze: if `g L ≤ 1.7 L* + 2` for all lists and for every `k ≥ 1` some list with
`L* = k` has `g L > 1.7 k - 8`, the sup ratio tends to `17/10`. -/
theorem ratio_tendsto_of_bounds (g : List ℝ → ℕ) (A B : ℝ)
    (hup : ∀ L : List ℝ, IsList L → (g L : ℝ) ≤ 17 / 10 * (optBins L : ℝ) + A)
    (hlo : ∀ k : ℕ, 1 ≤ k → ∃ L : List ℝ, IsList L ∧ optBins L = k ∧
      17 / 10 * (k : ℝ) - B < (g L : ℝ)) :
    Tendsto (fun k : ℕ => ⨆ (L : List ℝ) (_ : IsList L) (_ : optBins L = k),
      (g L : ENNReal) / (k : ENNReal)) atTop (nhds ((17 : ENNReal) / 10)) := by
  have h17 : ENNReal.ofReal (17 / 10) = (17 : ENNReal) / 10 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hlim_up : Tendsto (fun k : ℕ => ENNReal.ofReal (17 / 10 + A / (k : ℝ))) atTop
      (nhds ((17 : ENNReal) / 10)) := by
    rw [← h17]
    apply ENNReal.tendsto_ofReal
    have := (tendsto_const_div_atTop_nhds_zero_nat A).const_add (17 / 10 : ℝ)
    simpa using this
  have hlim_lo : Tendsto (fun k : ℕ => ENNReal.ofReal (17 / 10 - B / (k : ℝ))) atTop
      (nhds ((17 : ENNReal) / 10)) := by
    rw [← h17]
    apply ENNReal.tendsto_ofReal
    have := (tendsto_const_div_atTop_nhds_zero_nat B).const_sub (17 / 10 : ℝ)
    simpa using this
  -- key conversion: (n : ℝ≥0∞) / k = ofReal (n / k) for k ≥ 1
  have hconv : ∀ (n k : ℕ), 1 ≤ k →
      (n : ENNReal) / (k : ENNReal) = ENNReal.ofReal ((n : ℝ) / (k : ℝ)) := by
    intro n k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    rw [ENNReal.ofReal_div_of_pos hkpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_lo hlim_up ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    obtain ⟨L, hL, hkL, hgt⟩ := hlo k hk
    refine le_iSup₂_of_le L hL (le_iSup_of_le hkL ?_)
    rw [hconv _ _ hk]
    apply ENNReal.ofReal_le_ofReal
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    rw [le_div_iff₀ hkpos, sub_mul, div_mul_cancel₀ _ hkpos.ne']
    linarith
  · filter_upwards [eventually_ge_atTop 1] with k hk
    refine iSup₂_le fun L hL => iSup_le fun hkL => ?_
    rw [hconv _ _ hk]
    apply ENNReal.ofReal_le_ofReal
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have h := hup L hL
    rw [hkL] at h
    rw [div_le_iff₀ hkpos, add_mul, div_mul_cancel₀ _ hkpos.ne']
    linarith

end BinPacking.FirstFit

open BinPacking.FirstFit in
theorem solution :
    Filter.Tendsto BinPacking.FirstFit.ratioFF Filter.atTop (nhds ((17 : ENNReal) / 10)) ∧
    Filter.Tendsto BinPacking.FirstFit.ratioBF Filter.atTop (nhds ((17 : ENNReal) / 10)) := by
  constructor
  · exact ratio_tendsto_of_bounds FF 2 8
      (fun L hL => (ff_bf_le_seventeen_tenths L hL).1)
      (fun k hk => by
        obtain ⟨L, hL, hk', _, hgt⟩ := ff_eq_bf_gt_seventeen_tenths_sub_eight k hk
        exact ⟨L, hL, hk', hgt⟩)
  · exact ratio_tendsto_of_bounds BF 2 8
      (fun L hL => (ff_bf_le_seventeen_tenths L hL).2)
      (fun k hk => by
        obtain ⟨L, hL, hk', hFB, hgt⟩ := ff_eq_bf_gt_seventeen_tenths_sub_eight k hk
        exact ⟨L, hL, hk', hFB ▸ hgt⟩)
