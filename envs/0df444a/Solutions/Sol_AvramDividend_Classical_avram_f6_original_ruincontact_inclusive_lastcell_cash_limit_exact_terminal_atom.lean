-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_ruincontact_inclusive_lastcell_cash_limit_exact_terminal_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:52:41.536441+00:00
-- url     : https://prove2.me/submissions/d1bf9b7d-4d2b-4b62-ab3d-04ac25cef96e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_ruincontact_full_final_Ioc_cash_strict_tail_plus_exact_atom
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_ruincontact_canonical_n_mesh_strict_stieltjes_cash_tail_zero
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
  let A : ℕ → ℝ≥0∞ := fun j =>
    ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  let F : ℕ → ℝ≥0∞ := fun j =>
    ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  let B : ℝ≥0∞ :=
    ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ {(T : ℝ)},
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  change Tendsto F atTop (nhds B)
  have hSplit : ∀ j : ℕ, F j = A j + B := by
    intro j
    exact avram_f6_original_ruincontact_full_final_Ioc_cash_strict_tail_plus_exact_atom
      X x D ω T q n hn j
  have hTail : Tendsto A atTop (nhds (0 : ℝ≥0∞)) :=
    avram_f6_original_ruincontact_canonical_n_mesh_strict_stieltjes_cash_tail_zero
      X x D hD ω T q hq n hn
  have hFn : F = fun j => A j + B := funext hSplit
  rw [hFn]
  simpa only [zero_add] using hTail.add (tendsto_const_nhds (x := B))
