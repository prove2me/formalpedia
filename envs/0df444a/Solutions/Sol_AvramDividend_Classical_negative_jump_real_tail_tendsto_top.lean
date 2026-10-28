-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_real_tail_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:12:05.260746+00:00
-- url     : https://prove2.me/submissions/7317b42f-2324-4f97-9166-17a724d8d913

import Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Defs

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal
theorem solution
    (ν : Measure ℝ)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤) :
    Tendsto (fun x : ℝ => (ν (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by 
  have hT : Tendsto (fun n : ℕ => ν (Iic (-(1 / ((n : ℝ) + 1))))) atTop (nhds (⊤ : ℝ≥0∞)) := by
    have hmono : Monotone (fun n : ℕ => Iic (-(1 / ((n : ℝ) + 1)))) := by
      intro m n hmn
      apply Iic_subset_Iic.mpr
      have : (m : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      have h0 : (0:ℝ) < m + 1 := by positivity
      have := one_div_le_one_div_of_le h0 this
      linarith
    have hU : (⋃ n : ℕ, Iic (-(1 / ((n : ℝ) + 1)))) = Iio 0 := by
      ext y
      simp only [mem_iUnion, mem_Iic, mem_Iio]
      constructor
      · rintro ⟨n, hn⟩
        have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        linarith
      · intro hy
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hy)
        exact ⟨n, by linarith⟩
    have := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rw [hU, hνinf] at this
    exact this
  have hfin : ∀ c : ℝ, 0 < c → ν (Iio (-c)) ≠ ⊤ := by
    intro c hc0
    have hle : ENNReal.ofReal (min 1 (c ^ 2)) * ν (Iio (-c)) ≤ ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν := by
      rw [← setLIntegral_const]
      refine le_trans (setLIntegral_mono' measurableSet_Iio ?_) (setLIntegral_le_lintegral _ _)
      intro y hy
      simp only [mem_Iio] at hy
      apply ENNReal.ofReal_le_ofReal
      apply min_le_min le_rfl
      nlinarith
    have hpos : ENNReal.ofReal (min 1 (c ^ 2)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    intro htop
    rw [htop, ENNReal.mul_top hpos] at hle
    exact absurd (lt_of_le_of_lt hle hνint) (lt_irrefl _)
  rw [tendsto_atTop]
  intro b
  obtain ⟨n, hn⟩ := (hT.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top (r := b)))).exists
  have hn0 : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hn0] with x hx
  have hsub : Iic (-(1 / ((n : ℝ) + 1))) ⊆ Iio (-x) := by
    intro y hy; simp only [mem_Iic, mem_Iio] at *; linarith [hx.2]
  have h1 := lt_of_lt_of_le hn (measure_mono hsub)
  exact ((ENNReal.ofReal_le_iff_le_toReal (hfin x hx.1)).1 h1.le)
