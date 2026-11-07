-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_nested_C2_supremum_preexit_riskProcess_finite_discounted_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:48:14.970462+00:00
-- url     : https://prove2.me/submissions/81ca0869-5460-4dd0-915d-9e74797f5844

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_finite_lebesgue_energy

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
    ∀ (ω : Ω) (T : ℝ≥0), (T : WithTop ℝ≥0) < ⨆ n, τ n ω →
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
  dsimp only
  intro ω T hT
  obtain ⟨n, hTn⟩ : ∃ n : ℕ,
      (T : WithTop ℝ≥0) < min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0) :=
    lt_iSup_iff.mp hT
  obtain ⟨M, hM, hfin⟩ :=
    avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_finite_lebesgue_energy
      X x D hD C w hw q hq r (lower n) (upper n)
      (hlower n) (hband n) (hcap n) hdense (B n)
  refine ⟨n, M, hM, le_of_lt hTn, ?_⟩
  intro A hA hAfin hAsub
  exact hfin ω T (le_of_lt hTn) A hA hAfin hAsub
