-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_original_nested_C2_clock_and_preexit_discounted_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:42:05.535198+00:00
-- url     : https://prove2.me/submissions/be59d57b-685d-45b0-acc9-a8e368706908

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_bounded_C2_stop_sequence_covers_its_supremum
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_C2_supremum_preexit_riskProcess_finite_discounted_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The SAME original physical nested clocks have the stopping and
    monotone coverage properties and source-specific discounted C2 energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (lower upper : ℕ → ℝ) (B : ℕ → ℝ≥0)
    (hlower : ∀ n, 0 < lower n)
    (hband : ∀ n, lower n ≤ upper n)
    (hlo : ∀ n, lower (n + 1) ≤ lower n)
    (hup : ∀ n, upper n ≤ upper (n + 1))
    (hcap : ∀ n, ∀ y ∈ Set.Icc (lower n) (upper n), ENNReal.ofReal y < C)
    (hB : ∀ n, B n ≤ B (n + 1)) :
    let τ : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)
    let τSup : Ω → WithTop ℝ≥0 := fun ω => ⨆ n, τ n ω
    (∀ n, IsStoppingTime 𝓕.rightCont (τ n)) ∧
      (∀ n ω, τ n ω ≤ τ (n + 1) ω) ∧
      (∀ ω (t : WithTop ℝ≥0), t < τSup ω ↔ ∃ n, t < τ n ω) ∧
      ∀ (ω : Ω) (T : ℝ≥0), (T : WithTop ℝ≥0) < τSup ω →
        ∃ (n : ℕ) (M : ℝ), 0 ≤ M ∧
          (T : WithTop ℝ≥0) ≤ τ n ω ∧
          ∀ (A : Set ℝ), MeasurableSet A →
            (volume : Measure ℝ) A < ⊤ →
            (∀ t ∈ A, 0 ≤ t ∧ t.toNNReal < T) →
            let E : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal
              (|Real.exp (-(q * (t.toNNReal : ℝ))) *
                  w (riskProcess X x D t.toNNReal ω)| +
                |Real.exp (-(q * (t.toNNReal : ℝ))) *
                  deriv w (riskProcess X x D t.toNNReal ω)| +
                |Real.exp (-(q * (t.toNNReal : ℝ))) *
                  deriv (deriv w) (riskProcess X x D t.toNNReal ω)|)
            (∫⁻ t : ℝ, A.indicator E t ∂(volume : Measure ℝ)) < ⊤ := by
  have hc := avram_wave7_18_original_nested_bounded_C2_stop_sequence_covers_its_supremum
    X x D hD C w hw r hdense lower upper B hlower hlo hup hcap hB
  have he := avram_wave7_18_original_nested_C2_supremum_preexit_riskProcess_finite_discounted_energy
    X x D hD C w hw q hq r hdense lower upper B hlower hband hlo hup hcap hB
  exact ⟨hc.1, hc.2.1, hc.2.2, he⟩
