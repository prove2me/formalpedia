-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_ae_cofinal_payment_residual_from_chronological_timing_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:26:36.698826+00:00
-- url     : https://prove2.me/submissions/ff575e3f-2092-4ed7-a6e7-97b3c7da1830

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_cofinal_ruinstopped_payment_timing_mesh_vanishes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- Almost-sure original-source Stieltjes residual upper obtained by
    absorbing the same cofinal stopped payment timing error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hu : ∀ n, Monotone (u n)) (hzero : ∀ n, u n 0 = 0)
    (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (Residual : ℕ → Ω → ℝ) (Cash H : Ω → ℝ)
    (Timing : ℕ → Ω → ℝ)
    (hTiming : ∀ n ω, Timing n ω =
      (let v : ℕ → ℝ≥0 := fun i => min (u (φ n) i) (τ ω)
       ∑ i ∈ Finset.range (k (φ n)),
         (Real.exp (-(q * (v i : ℝ))) -
           Real.exp (-(q * (v (i + 1) : ℝ)))) *
           |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
             w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|))
    (hLocal : ∀ᵐ ω ∂P, ∃ L a b : ℝ,
      0 ≤ L ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |w s - w t| ≤ L * |s - t|) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b))
    (hChronological : ∀ᵐ ω ∂P, ∀ n,
      Residual (φ n) ω + Cash ω ≤ H ω + Timing n ω)
    (hmesh0 : Tendsto m atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, Residual (φ n) ω + Cash ω ≤ H ω + ε := by
  filter_upwards [hLocal, hChronological] with ω hω hchrono
  obtain ⟨L, a, b, hL, hLip, hPre, hPost⟩ := hω
  let Err : ℕ → ℝ := fun n =>
    let v : ℕ → ℝ≥0 := fun i => min (u (φ n) i) (τ ω)
    ∑ i ∈ Finset.range (k (φ n)),
      (Real.exp (-(q * (v i : ℝ))) -
        Real.exp (-(q * (v (i + 1) : ℝ)))) *
        |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
          w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|
  have hlim : Tendsto Err atTop (𝓝 0) := by
    simpa only [Err] using
      (avram_wave6_06_original_cofinal_ruinstopped_payment_timing_mesh_vanishes
        X x D hD ω τ u k hu hzero m hm hmesh q hq w L hL a b
        hLip hPre hPost hmesh0 φ hφ)
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, Err n < ε :=
    hlim.eventually (isOpen_Iio.mem_nhds hε)
  filter_upwards [hsmall] with n hn
  have hbound : Residual (φ n) ω + Cash ω ≤ H ω + Err n := by
    simpa only [hTiming n ω, Err] using hchrono n
  linarith
