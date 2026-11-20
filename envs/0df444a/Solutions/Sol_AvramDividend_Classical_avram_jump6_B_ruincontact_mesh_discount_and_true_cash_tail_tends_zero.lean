-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_ruincontact_mesh_discount_and_true_cash_tail_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:52:16.339025+00:00
-- url     : https://prove2.me/submissions/c9b3cac1-b093-438e-94b8-8aa11f2ec947

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn11_original_masked_strict_contact_cash_toReal_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (hn : 0 < n) :
    Tendsto (fun j : ℕ =>
      q * ((n : ℝ) / ((j : ℝ) + 1)) * Real.exp (q * (n : ℝ)) *
        rightLimit D t ω +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((t : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
      atTop (𝓝 (0 : ℝ)) := by
  let δ : ℕ → ℝ := fun j => (n : ℝ) / ((j : ℝ) + 1)
  have hδpos : ∀ j, 0 < δ j := by
    intro j
    change 0 < (n : ℝ) / ((j : ℝ) + 1)
    exact div_pos (by exact_mod_cast hn) (by positivity)
  have hδanti : Antitone δ := by
    intro i j hij
    have hden : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
      exact_mod_cast Nat.add_le_add_right hij 1
    have hfrac : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hden
    change (n : ℝ) / ((j : ℝ) + 1) ≤ (n : ℝ) / ((i : ℝ) + 1)
    calc
      (n : ℝ) / ((j : ℝ) + 1) =
          (n : ℝ) * (1 / ((j : ℝ) + 1)) := by ring
      _ ≤ (n : ℝ) * (1 / ((i : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = (n : ℝ) / ((i : ℝ) + 1) := by ring
  have hδ : Tendsto δ atTop (𝓝 (0 : ℝ)) := by
    have hbase : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul : Tendsto (fun j : ℕ => (n : ℝ) * (1 / ((j : ℝ) + 1)))
        atTop (𝓝 ((n : ℝ) * 0)) :=
      tendsto_const_nhds.mul hbase
    simpa only [mul_zero, div_eq_mul_inv, one_mul, δ] using hmul
  have hTail := avram_bv_env3_turn11_original_masked_strict_contact_cash_toReal_zero
    X x D hD ω q hq t t (le_refl _) δ hδpos hδanti hδ
  have hterm : Tendsto
      (fun j : ℕ => q * δ j * Real.exp (q * (n : ℝ)) * rightLimit D t ω)
      atTop (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun j : ℕ => q * δ j)
        atTop (𝓝 (q * (0 : ℝ))) := tendsto_const_nhds.mul hδ
    have h2 : Tendsto (fun j : ℕ => q * δ j * Real.exp (q * (n : ℝ)))
        atTop (𝓝 ((q * (0 : ℝ)) * Real.exp (q * (n : ℝ)))) :=
      h1.mul tendsto_const_nhds
    have h3 : Tendsto
        (fun j : ℕ => q * δ j * Real.exp (q * (n : ℝ)) * rightLimit D t ω)
        atTop (𝓝 ((q * (0 : ℝ)) * Real.exp (q * (n : ℝ)) *
          rightLimit D t ω)) := h2.mul tendsto_const_nhds
    simpa only [mul_zero, zero_mul] using h3
  simpa only [δ, zero_add] using hterm.add hTail
