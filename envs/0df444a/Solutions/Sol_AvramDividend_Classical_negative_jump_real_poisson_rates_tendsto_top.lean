-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_real_poisson_rates_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:45:28.74804+00:00
-- url     : https://prove2.me/submissions/67f335b7-4f04-4358-832b-e70b5cf96b74

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Order.Filter.AtTopBot.Field

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Finite jump-band rates at every positive time horizon diverge under infinite activity. -/
theorem solution
    (ν : Measure ℝ)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤)
    (t : ℝ) (ht : 0 < t) :
    Tendsto
      (fun n : ℕ => t * (ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
      atTop atTop := by 
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
  have hfin : ∀ n : ℕ, ν (Iic (-(1 / ((n : ℝ) + 1)))) ≠ ⊤ := by
    intro n
    set c : ℝ := 1 / ((n : ℝ) + 1) with hc
    have hc0 : 0 < c := by positivity
    have hc1 : c ≤ 1 := by
      rw [hc, div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hle : ENNReal.ofReal (c ^ 2) * ν (Iic (-c)) ≤ ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν := by
      rw [← setLIntegral_const]
      refine le_trans (setLIntegral_mono' measurableSet_Iic ?_) (setLIntegral_le_lintegral _ _)
      intro y hy
      simp only [mem_Iic] at hy
      apply ENNReal.ofReal_le_ofReal
      apply le_min
      · nlinarith
      · nlinarith
    have hpos : ENNReal.ofReal (c ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    intro htop
    rw [htop, ENNReal.mul_top hpos] at hle
    exact absurd (lt_of_le_of_lt hle hνint) (lt_irrefl _)
  have hR : Tendsto (fun n : ℕ => (ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    have hb : ENNReal.ofReal b < ⊤ := ENNReal.ofReal_lt_top
    filter_upwards [hT.eventually (lt_mem_nhds hb)] with n hn
    have := (ENNReal.ofReal_le_iff_le_toReal (hfin n)).1 hn.le
    exact this
  exact hR.const_mul_atTop ht
