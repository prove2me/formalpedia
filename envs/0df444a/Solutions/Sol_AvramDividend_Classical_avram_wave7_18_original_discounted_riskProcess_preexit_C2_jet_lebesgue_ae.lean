-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_lebesgue_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:11.816209+00:00
-- url     : https://prove2.me/submissions/6ce16a31-d1e2-4140-8ea6-0e80b81432eb

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_discounted_stopped_C2_jet_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower) (hlu : lower ≤ upper)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hdense : DenseRange r) (B : ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤
          min (⨅ k : ℕ,
            if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
                upper < x + X.X (r k) ω - rightLimit D (r k) ω
            then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
        ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
          0 ≤ t → t.toNNReal < T →
          |Real.exp (-(q * (t.toNNReal : ℝ))) *
             w (riskProcess X x D t.toNNReal ω)| ≤ M ∧
          |Real.exp (-(q * (t.toNNReal : ℝ))) *
             deriv w (riskProcess X x D t.toNNReal ω)| ≤ M ∧
          |Real.exp (-(q * (t.toNNReal : ℝ))) *
             deriv (deriv w) (riskProcess X x D t.toNNReal ω)| ≤ M := by
  obtain ⟨M, hM, hdisc⟩ :=
    avram_wave7_18_original_discounted_stopped_C2_jet_uniform_bound
      X x D hD C w hw q hq r lower upper hlower hlu hcap hdense B
  refine ⟨M, hM, ?_⟩
  intro ω T hT
  have hae :=
    avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae
      X x D hD ω
  filter_upwards [hae] with t ht hnonneg htime
  rw [ht hnonneg]
  exact hdisc ω T hT t.toNNReal htime
