-- Prove2me | solution 2 for AvramDividend.Classical.avram_f6_original_ruincontact_inclusive_lastcell_cash_limit_exact_terminal_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:57:18.428354+00:00
-- url     : https://prove2.me/submissions/1d405b61-d05e-44b0-a352-fee836cf8075

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_discounted_masked_contact_tail_tendsto_endpoint_atom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (hn : 0 < n) :
    Tendsto (fun j : ℕ =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioc ((T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      atTop (nhds
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ {(T : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))) := by
  let δ : ℕ → ℝ := fun j => (n : ℝ) / ((j : ℝ) + 1)
  have hδpos : ∀ j, 0 < δ j := by
    intro j
    unfold δ
    exact div_pos (by exact_mod_cast hn) (by positivity)
  have hδanti : Antitone δ := by
    intro i j hij
    change (n : ℝ) / ((j : ℝ) + 1) ≤
      (n : ℝ) / ((i : ℝ) + 1)
    have hd : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hij 1
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  have hδ : Tendsto δ atTop (nhds (0 : ℝ)) := by
    simpa only [δ, mul_one_div, mul_zero] using
      (tendsto_const_nhds (x := (n : ℝ))).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [δ] using
    (avram_p3_grid4_original_discounted_masked_contact_tail_tendsto_endpoint_atom
      X x D hD ω q hq T T le_rfl δ hδpos hδanti hδ)
