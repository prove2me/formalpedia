-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_clipped_clock_lower_cutoff_expectation_budget_mct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:34:31.272055+00:00
-- url     : https://prove2.me/submissions/11109760-fd10-4953-88d7-e1c8189ad0c3


import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_clipped_clock_zero_atom_lower_cutoff_lintegral_iSup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (hn : ENNReal.ofReal T < (n : ℝ≥0∞)) (budget : ℝ≥0∞)
    (hMeas : ∀ k : ℕ, Measurable (fun ω : Ω =>
      (∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))))
    (hBound : ∀ k : ℕ,
      (∫⁻ ω, ((∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  classical
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let atom (ω : Ω) : ℝ≥0∞ := ∫⁻ t in ({0} : Set ℝ), f t ∂(dividendMeasure D ω)
  let cut (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
      Icc (1 / ((k : ℝ) + 1)) T, f t ∂(dividendMeasure D ω)
  let A (k : ℕ) (ω : Ω) : ℝ≥0∞ := atom ω + cut k ω
  let B (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      f t ∂(dividendMeasure D ω)
  have hpoint (ω : Ω) : B ω = ⨆ k : ℕ, A k ω := by
    dsimp [B, A, atom, cut, f]
    rw [avram_wave7_19_original_clipped_clock_zero_atom_lower_cutoff_lintegral_iSup
      X q x T hT D ω n hn, ENNReal.add_iSup]
  have hcut (k : ℕ) :
      (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) ≤ (1 : ℝ) / ((k : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast; linarith
  have hsub (k : ℕ) (ω : Ω) :
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T ⊆
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / (((k + 1 : ℕ) : ℝ) + 1)) T := by
    intro t ht
    exact ⟨ht.1, ⟨le_trans (hcut k) ht.2.1, ht.2.2⟩⟩
  have hmon : Monotone A := by
    apply monotone_nat_of_le_succ
    intro k ω
    change atom ω + cut k ω ≤ atom ω + cut (k + 1) ω
    exact add_le_add_right (lintegral_mono_set (hsub k ω)) (atom ω)
  have hm : ∀ k : ℕ, Measurable (A k) := by
    intro k; exact hMeas k
  have hb : ∀ k : ℕ, (∫⁻ ω, A k ω ∂P) ≤ budget := by
    intro k; exact hBound k
  change (∫⁻ ω, B ω ∂P) ≤ budget
  calc
    (∫⁻ ω, B ω ∂P) = ∫⁻ ω, ⨆ k : ℕ, A k ω ∂P := by
      apply lintegral_congr; exact hpoint
    _ = ⨆ k : ℕ, (∫⁻ ω, A k ω ∂P) := lintegral_iSup hm hmon
    _ ≤ budget := iSup_le hb
