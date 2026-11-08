-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian14_original_zerojump_common_stop_cauchy_terminal_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:48:39.081486+00:00
-- url     : https://prove2.me/submissions/05788773-cfdc-4ff2-9de5-01c6fe4a8e48

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian14_allnu_same_source_common_stop_cauchy_terminal_exists

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- In the no-jump branch, Cauchy original stopped Gaussian grids construct
their own centred L² terminal integral with no auxiliary source process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : ℕ → Finset ι) (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ (n : ℕ) (s : ℝ≥0),
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (B : ℕ → ℝ≥0) (hB : ∀ n ω, τ n ω ≤ B n)
    (h : ℕ → ι → ℝ≥0) (G : ℕ → ι → Ω → ℝ)
    (hGsource : ∀ n i, i ∈ S n → G n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (K : ℕ → ι → ℝ)
    (hK : ∀ n i, i ∈ S n → 0 ≤ K n i)
    (hGbound : ∀ n i, i ∈ S n → ∀ ω, |G n i ω| ≤ K n i) :
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω *
        ((X.X (τ n ω + h n i) ω - ((τ n ω + h n i) : ℝ) * X.c) -
         (X.X (τ n ω) ω - (τ n ω : ℝ) * X.c))
    Tendsto (fun nm : ℕ × ℕ => eLpNorm (Q nm.1 - Q nm.2) 2 P)
      atTop (𝓝 0) →
    ∃ L : Ω → ℝ, MemLp L 2 P ∧
      (∫ ω, L ω ∂P) = 0 ∧
      Tendsto (fun n => eLpNorm (Q n - L) 2 P) atTop (𝓝 0) := by
  have hDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (X.X t ω - (t : ℝ) * X.c) + (0 : ℝ) + 0 := by
    intro t ω
    ring
  simpa [sub_zero] using
    (avram_ubv_gaussian14_allnu_same_source_common_stop_cauchy_terminal_exists
      X X hν rfl (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
      hDecomp x D hD w C hw q T S τ hτ B hB h G hGsource K hK hGbound)
