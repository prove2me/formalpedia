-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_ruin_cash_zero_atom_lower_cutoff_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:12:54.885057+00:00
-- url     : https://prove2.me/submissions/2778eea5-d614-457f-86f5-5fd9dffd5b73

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_payment_zero_atom_reciprocal_lower_cutoff_iUnion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      ⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Icc (1 / ((n : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  classical
  let σ : ℝ≥0∞ := ruinTime X x D ω
  let A : ℕ → Set ℝ := fun n => paymentTimes σ ∩ Icc (1 / ((n : ℝ) + 1)) T
  let U : Set ℝ := ⋃ n : ℕ, A n
  let Afull : Set ℝ := paymentTimes σ ∩ Iic T
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let μ : Measure ℝ := dividendMeasure D ω
  have hUnion : Afull = ({0} : Set ℝ) ∪ U := by
    simpa only [Afull, U, A, σ] using
      (avram_wave7_19_original_ruin_payment_zero_atom_reciprocal_lower_cutoff_iUnion
        X x D ω T hT)
  have hA (n : ℕ) : MeasurableSet (A n) := by
    dsimp [A, paymentTimes]; measurability
  have hU : MeasurableSet U := MeasurableSet.iUnion hA
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hdisj : Disjoint ({0} : Set ℝ) U := by
    apply Set.disjoint_left.mpr
    intro t htzero htU
    have hz : t = 0 := by simpa using htzero
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp htU
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ t := hn.2.1
    subst t; linarith
  have hcut (n : ℕ) :
      (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast; linarith
  have hsub (n : ℕ) : A n ⊆ A (n + 1) := by
    intro t ht
    exact ⟨ht.1, ⟨le_trans (hcut n) ht.2.1, ht.2.2⟩⟩
  have hm (n : ℕ) : Measurable ((A n).indicator f) := hf.indicator (hA n)
  have hmon : Monotone (fun n : ℕ => (A n).indicator f) := by
    apply monotone_nat_of_le_succ
    intro n
    exact Set.indicator_le_indicator_of_subset (hsub n)
      (fun t => (show (0 : ℝ≥0∞) ≤ f t from zero_le))
  have hpoint (t : ℝ) : U.indicator f t = ⨆ n : ℕ, (A n).indicator f t := by
    change (⋃ n : ℕ, A n).indicator f t = _
    exact Set.indicator_iUnion_apply (by rfl) A f t
  have hlimit : (∫⁻ t in U, f t ∂μ) = ⨆ n : ℕ, (∫⁻ t in A n, f t ∂μ) := by
    calc
      (∫⁻ t in U, f t ∂μ) = ∫⁻ t, U.indicator f t ∂μ :=
        (lintegral_indicator hU f).symm
      _ = ∫⁻ t, (⨆ n : ℕ, (A n).indicator f t) ∂μ := by
        apply lintegral_congr; exact hpoint
      _ = ⨆ n : ℕ, ∫⁻ t, (A n).indicator f t ∂μ := lintegral_iSup hm hmon
      _ = ⨆ n : ℕ, ∫⁻ t in A n, f t ∂μ := by
        apply iSup_congr
        intro n
        exact lintegral_indicator (hA n) f
  change (∫⁻ t in Afull, f t ∂μ) =
    (∫⁻ t in ({0} : Set ℝ), f t ∂μ) + ⨆ n : ℕ, (∫⁻ t in A n, f t ∂μ)
  calc
    (∫⁻ t in Afull, f t ∂μ) =
        (∫⁻ t in ({0} : Set ℝ) ∪ U, f t ∂μ) := by rw [hUnion]
    _ = (∫⁻ t in ({0} : Set ℝ), f t ∂μ) +
        (∫⁻ t in U, f t ∂μ) := lintegral_union hU hdisj
    _ = (∫⁻ t in ({0} : Set ℝ), f t ∂μ) +
        ⨆ n : ℕ, (∫⁻ t in A n, f t ∂μ) := by rw [hlimit]
