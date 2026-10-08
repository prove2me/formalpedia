-- Prove2me | solution 1 for BinPacking.BoundedItems.ratio_limit_eq
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T16:54:21.017863+00:00
-- url     : https://prove2.me/submissions/e571b3fb-d211-435c-ad11-5f913edd8c43

import Theorems.Thm_BinPacking_BoundedItems_lower_bound
import Theorems.Thm_BinPacking_BoundedItems_ff_upper_bound
import Theorems.Thm_BinPacking_BoundedItems_bf_upper_bound

set_option autoImplicit false

open Filter Topology
open scoped ENNReal

namespace BinPacking.BoundedItems.RatioLimitProof

/-- The same order-topological squeeze applies to both packing rules. -/
theorem limit_of_bounds (A : List ℝ → ℕ) (α : ℝ) (m : ℕ) (hm : 0 < m)
    (hlo : ∀ k : ℕ, 1 ≤ k → ∃ L : List ℝ,
      IsList L ∧ (∀ a ∈ L, a ≤ α) ∧ optBins L = k ∧
      ((m : ℝ) + 1) / m * (optBins L : ℝ) - 1 / m ≤ (A L : ℝ))
    (hhi : ∀ L : List ℝ, IsList L → (∀ a ∈ L, a ≤ α) →
      (A L : ℝ) ≤ ((m : ℝ) + 1) / m * (optBins L : ℝ) + 2) :
    Tendsto (fun k : ℕ =>
      ⨆ (L : List ℝ) (_ : IsList L) (_ : ∀ a ∈ L, a ≤ α) (_ : optBins L = k),
        (A L : ℝ≥0∞) / (k : ℝ≥0∞))
      atTop (𝓝 (1 + (m : ℝ≥0∞)⁻¹)) := by
  let r : ℝ := ((m : ℝ) + 1) / m
  let R : ℕ → ℝ≥0∞ := fun k =>
    ⨆ (L : List ℝ) (_ : IsList L) (_ : ∀ a ∈ L, a ≤ α) (_ : optBins L = k),
      (A L : ℝ≥0∞) / (k : ℝ≥0∞)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlower : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (r - (1 / (m : ℝ)) / k) ≤ R k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    obtain ⟨L, hL, hLα, hopt, hbound⟩ := hlo k hk
    have hquot : r - (1 / (m : ℝ)) / k ≤ (A L : ℝ) / k := by
      apply (le_div_iff₀ hkR).mpr
      calc
        (r - (1 / (m : ℝ)) / k) * k = r * k - 1 / m := by
          rw [sub_mul, div_mul_cancel₀ _ hkR.ne']
        _ ≤ (A L : ℝ) := by simpa only [hopt] using hbound
    apply (ENNReal.ofReal_le_ofReal hquot).trans
    rw [ENNReal.ofReal_div_of_pos hkR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    exact le_iSup_of_le L (le_iSup_of_le hL (le_iSup_of_le hLα (le_iSup_of_le hopt le_rfl)))
  have hupper : ∀ᶠ k : ℕ in atTop,
      R k ≤ ENNReal.ofReal (r + 2 / (k : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    refine iSup_le fun L => iSup_le fun hL => iSup_le fun hLα => iSup_le fun hopt => ?_
    have hquot : (A L : ℝ) / k ≤ r + 2 / (k : ℝ) := by
      apply (div_le_iff₀ hkR).mpr
      calc
        (A L : ℝ) ≤ r * k + 2 := by simpa only [hopt] using hhi L hL hLα
        _ = (r + 2 / (k : ℝ)) * k := by
          rw [add_mul, div_mul_cancel₀ _ hkR.ne']
    have h := ENNReal.ofReal_le_ofReal hquot
    simpa only [ENNReal.ofReal_div_of_pos hkR, ENNReal.ofReal_natCast] using h
  have hloLim : Tendsto (fun k : ℕ => r - (1 / (m : ℝ)) / k) atTop (𝓝 r) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := r)).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1 / (m : ℝ)))
  have hhiLim : Tendsto (fun k : ℕ => r + 2 / (k : ℝ)) atTop (𝓝 r) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := r)).add
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  have hlimit : ENNReal.ofReal r = 1 + (m : ℝ≥0∞)⁻¹ := by
    have hr : r = 1 + (m : ℝ)⁻¹ := by
      dsimp [r]
      field_simp
    rw [hr, ENNReal.ofReal_add (by norm_num) (inv_nonneg.mpr hmR.le),
      ENNReal.ofReal_one, ENNReal.ofReal_inv_of_pos hmR, ENNReal.ofReal_natCast]
  simpa only [hlimit] using
    (ENNReal.tendsto_ofReal hloLim).squeeze' (ENNReal.tendsto_ofReal hhiLim) hlower hupper

end BinPacking.BoundedItems.RatioLimitProof

open BinPacking.BoundedItems in
theorem solution (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    Tendsto (ratioFF α) atTop (𝓝 (1 + ((⌊α⁻¹⌋₊ : ℕ) : ℝ≥0∞)⁻¹)) ∧
      Tendsto (ratioBF α) atTop (𝓝 (1 + ((⌊α⁻¹⌋₊ : ℕ) : ℝ≥0∞)⁻¹)) := by
  have hm2 : 2 ≤ ⌊α⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [inv_eq_one_div, le_div_iff₀ hα]
    norm_num
    linarith
  have hm : 0 < ⌊α⁻¹⌋₊ := lt_of_lt_of_le (by decide : 0 < 2) hm2
  constructor
  · exact RatioLimitProof.limit_of_bounds FF α ⌊α⁻¹⌋₊ hm
      (fun k hk => (lower_bound α hα hα2 _ rfl k hk).1)
      (ff_upper_bound α hα hα2 _ rfl)
  · exact RatioLimitProof.limit_of_bounds BF α ⌊α⁻¹⌋₊ hm
      (fun k hk => (lower_bound α hα hα2 _ rfl k hk).2)
      (bf_upper_bound α hα hα2 _ rfl)
