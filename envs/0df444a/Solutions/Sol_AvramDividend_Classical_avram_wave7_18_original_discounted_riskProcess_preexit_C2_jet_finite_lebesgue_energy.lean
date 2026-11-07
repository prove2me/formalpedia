-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_finite_lebesgue_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:57:48.042573+00:00
-- url     : https://prove2.me/submissions/188f55b5-db3f-4308-b761-835cdcd60c3b

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_lebesgue_ae

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
  obtain ⟨M, hM, hJet⟩ :=
    avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_lebesgue_ae
      X x D hD C w hw q hq r lower upper hlower hlu hcap hdense B
  refine ⟨M, hM, ?_⟩
  intro ω T hT A hA hAfin hAsub
  dsimp only
  let E : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal
    (|Real.exp (-(q * (t.toNNReal : ℝ))) *
        w (riskProcess X x D t.toNNReal ω)| +
      |Real.exp (-(q * (t.toNNReal : ℝ))) *
        deriv w (riskProcess X x D t.toNNReal ω)| +
      |Real.exp (-(q * (t.toNNReal : ℝ))) *
        deriv (deriv w) (riskProcess X x D t.toNNReal ω)|)
  have hae : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
      A.indicator E t ≤
        A.indicator (fun _ => ENNReal.ofReal (3 * M)) t := by
    filter_upwards [hJet ω T hT] with t ht
    by_cases h : t ∈ A
    · obtain ⟨hpos, htime⟩ := hAsub t h
      obtain ⟨h0, h1, h2⟩ := ht hpos htime
      have hsum :
          |Real.exp (-(q * (t.toNNReal : ℝ))) *
              w (riskProcess X x D t.toNNReal ω)| +
            |Real.exp (-(q * (t.toNNReal : ℝ))) *
              deriv w (riskProcess X x D t.toNNReal ω)| +
            |Real.exp (-(q * (t.toNNReal : ℝ))) *
              deriv (deriv w) (riskProcess X x D t.toNNReal ω)| ≤
            3 * M := by linarith
      simp only [Set.indicator_of_mem h]
      exact ENNReal.ofReal_le_ofReal hsum
    · simp only [Set.indicator_of_notMem h]
      exact le_refl (0 : ℝ≥0∞)
  have hfinite : (volume : Measure ℝ) A *
      ENNReal.ofReal (3 * M) < ⊤ :=
    ENNReal.mul_lt_top hAfin ENNReal.ofReal_lt_top
  calc
    (∫⁻ t : ℝ, A.indicator E t ∂(volume : Measure ℝ)) ≤
      ∫⁻ t : ℝ, A.indicator
        (fun _ => ENNReal.ofReal (3 * M)) t
        ∂(volume : Measure ℝ) :=
          lintegral_mono_ae hae
    _ = (volume : Measure ℝ) A * ENNReal.ofReal (3 * M) := by
      rw [lintegral_indicator_const hA]
      rw [mul_comm]
    _ < ⊤ := hfinite
