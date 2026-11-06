-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_positive_ruin_masked_tail_intersection_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:14:52.939124+00:00
-- url     : https://prove2.me/submissions/70a5258b-f97e-43e7-a9c4-aa39c5a3405b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual strict payment masking removes the only possible point in shrinking positive-ruin tails. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (τ : ℝ≥0)
    (hτ : 0 < τ)
    (hruin : (τ : ℝ≥0∞) = ruinTime X x D ω)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    (⋂ n : ℕ, paymentTimes (ruinTime X x D ω) ∩
      Ioc ((τ : ℝ) - δ n) (τ : ℝ)) = ∅ := by
  have hNot : (τ : ℝ) ∉ paymentTimes (ruinTime X x D ω) := by
    intro hmem
    rcases hmem with ⟨_, hzero | hlt⟩
    · have hpos : (0 : ℝ) < (τ : ℝ) := by exact_mod_cast hτ
      exact (ne_of_gt hpos) hzero
    · have hcoe : ENNReal.ofReal (τ : ℝ) = (τ : ℝ≥0∞) := by simp
      exact (ne_of_lt hlt) (hcoe.trans hruin)
  ext t
  constructor
  · intro ht
    have htAll (n : ℕ) :
        t ∈ paymentTimes (ruinTime X x D ω) ∩
          Ioc ((τ : ℝ) - δ n) (τ : ℝ) :=
      Set.mem_iInter.mp ht n
    have hUpper : t ≤ (τ : ℝ) := (htAll 0).2.2
    rcases lt_or_eq_of_le hUpper with hlt | heq
    · have hgap : (0 : ℝ) < (τ : ℝ) - t := sub_pos.mpr hlt
      have hEventually : ∀ᶠ n : ℕ in atTop, δ n < (τ : ℝ) - t :=
        hδ.eventually (isOpen_Iio.mem_nhds hgap)
      obtain ⟨n, hn⟩ := hEventually.exists
      have hLower : (τ : ℝ) - δ n < t := (htAll n).2.1
      linarith
    · have hPay : (τ : ℝ) ∈ paymentTimes (ruinTime X x D ω) := by
        simpa only [heq] using (htAll 0).1
      exact (hNot hPay).elim
  · intro ht
    simp at ht
