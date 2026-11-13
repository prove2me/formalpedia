-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_strict_cash_grid_limit_of_discount_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:31:23.642101+00:00
-- url     : https://prove2.me/submissions/658b4db4-00f6-462c-992d-e46820b01d34

import Theorems.Thm_AvramDividend_Classical_avram_chat24_original_strict_cash_finite_partition_real_brackets
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
open Finset

lemma strict_cash_upper_sums_tendsto
    (upper lower mesh : ℕ → ℝ) (cash K : ℝ)
    (hlo : ∀ n, lower n ≤ cash) (hup : ∀ n, cash ≤ upper n)
    (hgap : ∀ n, upper n ≤ lower n + K * mesh n)
    (hmesh : Tendsto mesh atTop (nhds 0)) :
    Tendsto upper atTop (nhds cash) := by
  have herr : Tendsto (fun n => K * mesh n) atTop (nhds 0) := by
    simpa only [mul_zero] using hmesh.const_mul K
  have hz : Tendsto (fun n => upper n - cash) atTop (nhds 0) := by
    have hle (n : ℕ) : upper n - cash ≤ K * mesh n := by
      linarith [hgap n, hlo n]
    exact squeeze_zero (fun n => sub_nonneg.mpr (hup n)) hle herr
  have h := hz.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => cash) atTop (nhds cash))
  simpa only [sub_add_cancel, zero_add] using h

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (B : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hu : ∀ n, Monotone (u n)) (hu0 : ∀ n, u n 0 = 0)
    (huN : ∀ n, u n (N n) = B)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hdiscount : ∀ n i, i < N n →
      Real.exp (-(q * (u n i : ℝ))) - Real.exp (-(q * (u n (i + 1) : ℝ))) ≤ q * mesh n) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      Real.exp (-(q * (u n i : ℝ))) * (D (u n (i + 1)) ω - D (u n i) ω))
      atTop (nhds ((∫⁻ t in Ico (0 : ℝ) (B : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by
  classical
  let cash : ℝ := (∫⁻ t in Ico (0 : ℝ) (B : ℝ),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let d : ℕ → ℕ → ℝ := fun n i => D (u n (i + 1)) ω - D (u n i) ω
  let upper : ℕ → ℝ := fun n => ∑ i ∈ range (N n),
    Real.exp (-(q * (u n i : ℝ))) * d n i
  let lower : ℕ → ℝ := fun n => ∑ i ∈ range (N n),
    Real.exp (-(q * (u n (i + 1) : ℝ))) * d n i
  have hb (n : ℕ) : lower n ≤ cash ∧ cash ≤ upper n := by
    have h := avram_chat24_original_strict_cash_finite_partition_real_brackets D hD ω q hq (u n) (hu n) (N n)
    simpa only [lower, upper, cash, d, hu0, huN, NNReal.coe_zero] using h.2
  have htel (n k : ℕ) : (∑ i ∈ range k, d n i) = D (u n k) ω - D (u n 0) ω := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih]; dsimp [d]; ring
  have hgap (n : ℕ) : upper n ≤ lower n + (q * D B ω) * mesh n := by
    have hs : upper n ≤ lower n + q * mesh n * (∑ i ∈ range (N n), d n i) := by
      calc
        upper n ≤ ∑ i ∈ range (N n),
            (Real.exp (-(q * (u n (i + 1) : ℝ))) * d n i + q * mesh n * d n i) := by
          apply sum_le_sum
          intro i hi
          have hd : 0 ≤ d n i := sub_nonneg.mpr (hD.2.1 ω (hu n (Nat.le_succ i)))
          have he := mul_le_mul_of_nonneg_right (hdiscount n i (mem_range.mp hi)) hd
          dsimp only [upper] at *
          nlinarith
        _ = _ := by rw [sum_add_distrib, ← mul_sum]
    have ht : (∑ i ∈ range (N n), d n i) = D B ω := by
      rw [htel, huN, hu0, hD.1 ω, sub_zero]
    rw [ht] at hs
    nlinarith
  exact strict_cash_upper_sums_tendsto upper lower mesh cash (q * D B ω)
    (fun n => (hb n).1) (fun n => (hb n).2) hgap hmesh

