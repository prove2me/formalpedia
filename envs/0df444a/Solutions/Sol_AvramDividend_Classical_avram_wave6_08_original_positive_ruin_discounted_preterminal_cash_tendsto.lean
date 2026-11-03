-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_ruin_discounted_preterminal_cash_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:54:09.948851+00:00
-- url     : https://prove2.me/submissions/22e8df10-418f-49fc-8940-9e1c592626c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_discounted_cash_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_discounted_strict_interior_mass_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_discounted_strict_ruin_terminal_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The genuine full discounted right-payment cash along a pre-ruin grid
converges to all strictly pre-ruin payments, with no ruin right atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < τ)
    (hlim : Tendsto u atTop (𝓝 τ)) :
    Tendsto (fun n => ∫⁻ t in Ioc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let total : ℝ≥0∞ := ∫⁻ t in Ioo (0 : ℝ) (τ : ℝ), f t ∂μ
  let preCash : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ t in Ioc (0 : ℝ) (u n : ℝ), f t ∂μ
  let tail : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ t in Ioo (u n : ℝ) (τ : ℝ), f t ∂μ
  have hfin : total < ⊤ :=
    avram_wave6_08_original_positive_ruin_strict_discounted_cash_lt_top
      D hD ω q hq τ hτ
  have htail : Tendsto tail atTop (𝓝 0) :=
    avram_wave6_08_original_positive_ruin_discounted_strict_interior_mass_vanish
      D hD ω q hq τ hτ u hu hlim
  have hupos : ∀ᶠ n : ℕ in atTop, (0 : ℝ≥0) < u n := by
    simpa only [mem_Ioi] using
      (hlim.eventually (isOpen_Ioi.mem_nhds hτ))
  have hsplit (n : ℕ) (hn : 0 < u n) :
      total = preCash n + tail n :=
    avram_wave6_08_original_discounted_strict_ruin_terminal_partition
      D hD ω q hq 0 (u n) τ hn (hu n)
  have hsub : Tendsto (fun n => total - tail n) atTop (𝓝 total) := by
    have hpair : Tendsto (fun n : ℕ => (total, tail n))
        atTop (𝓝 (total, (0 : ℝ≥0∞))) :=
      by simpa only [nhds_prod_eq] using (tendsto_const_nhds.prodMk htail)
    have hs := (ENNReal.tendsto_sub (Or.inl (ne_of_lt hfin))).comp hpair
    have hzero : total - (0 : ℝ≥0∞) = total := by simp
    rw [hzero] at hs
    simpa only [Function.comp_def] using hs
  have heq : ∀ᶠ n : ℕ in atTop, preCash n = total - tail n := by
    filter_upwards [hupos] with n hn
    have htne : tail n ≠ ⊤ := by
      intro ht
      have htop : total = ⊤ := by
        calc
          total = preCash n + tail n := hsplit n hn
          _ = ⊤ := by simp [ht]
      exact (ne_of_lt hfin) htop
    calc
      preCash n = (preCash n + tail n) - tail n :=
        (ENNReal.add_sub_cancel_right htne).symm
      _ = total - tail n := by rw [← hsplit n hn]
  change Tendsto preCash atTop (𝓝 total)
  have heq' : (fun n => total - tail n) =ᶠ[atTop] preCash := by
    filter_upwards [heq] with n hn
    exact hn.symm
  exact hsub.congr' heq'
