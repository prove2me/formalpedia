-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_cofinal_ruinstopped_payment_timing_mesh_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:20:57.468493+00:00
-- url     : https://prove2.me/submissions/7caed1a2-0c61-4bd7-8b00-dfbf2c749754

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_stopped_prepostpayment_discount_mesh_error_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- The literal original ruin-stopped payment timing mesh error remains negligible
    along the same cofinal source subsequence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hu : ∀ n, Monotone (u n)) (hzero : ∀ n, u n 0 = 0)
    (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ L * |s - t|)
    (hPre : ∀ n i, i < k n →
      x + X.X (min (u n (i + 1)) (τ ω)) ω -
        rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b)
    (hPost : ∀ n i, i < k n →
      x + X.X (min (u n (i + 1)) (τ ω)) ω -
        rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b)
    (hmesh0 : Tendsto m atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun n =>
      let v : ℕ → ℝ≥0 := fun i => min (u (φ n) i) (τ ω)
      ∑ i ∈ Finset.range (k (φ n)),
        (Real.exp (-(q * (v i : ℝ))) -
          Real.exp (-(q * (v (i + 1) : ℝ)))) *
          |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
            w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|)
      atTop (𝓝 0) := by
  have hbase :=
    avram_wave6_06_original_stopped_prepostpayment_discount_mesh_error_tendsto
      X x D hD ω τ u k hu hzero m hm hmesh q hq w L hL a b hLip
      hPre hPost hmesh0
  simpa only [Function.comp_def] using hbase.comp hφ
