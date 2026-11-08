-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_same_source_grid_limit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:42:42.501723+00:00
-- url     : https://prove2.me/submissions/8ad751e9-cfe6-42c9-b180-4b299a665386

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! The pathwise Brownian projection stays on the original sample space.
Finite predictable-step means and a bounded almost-sure limit give the stopped mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge B : ℝ≥0 → Ω → ℝ)
    (hDecomp : ∀ ω t, X.X t ω =
      (t : ℝ) * X.c + (Y.X t ω - (t : ℝ) * Y.c) +
      Jsmall t ω + Jlarge t ω)
    (hB : ∀ ω t, B t ω = X.X t ω - (t : ℝ) * X.c -
      Jsmall t ω - Jlarge t ω)
    (S : ℕ → Finset ℕ)
    (u v : ℕ → ℕ → Ω → ℝ≥0)
    (G : ℕ → ℕ → Ω → ℝ)
    (F : ℕ → Ω → ℝ)
    (hF : ∀ n ω, F n ω = ∑ i ∈ S n,
      G n i ω * (B (v n i ω) ω - B (u n i ω) ω))
    (hStepI : ∀ n i, i ∈ S n →
      Integrable (fun ω => G n i ω *
        (B (v n i ω) ω - B (u n i ω) ω)) P)
    (hStepZero : ∀ n i, i ∈ S n →
      (∫ ω, G n i ω *
        (B (v n i ω) ω - B (u n i ω) ω) ∂P) = 0)
    (K : ℝ) (hBound : ∀ n, ∀ᵐ ω ∂P, |F n ω| ≤ K)
    (M : Ω → ℝ)
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (M ω))) :
    (∀ ω t, B t ω = Y.X t ω - (t : ℝ) * Y.c) ∧
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hBridge : ∀ ω t, B t ω = Y.X t ω - (t : ℝ) * Y.c := by
    intro ω t
    rw [hB ω t, hDecomp ω t]
    ring
  have hEq (n : ℕ) : F n =ᵐ[P] (fun ω => ∑ i ∈ S n,
      G n i ω * (B (v n i ω) ω - B (u n i ω) ω)) := by
    exact Filter.Eventually.of_forall (hF n)
  have hFI (n : ℕ) : Integrable (F n) P := by
    have hsum : Integrable (fun ω =>
        ∑ i ∈ S n, G n i ω *
          (B (v n i ω) ω - B (u n i ω) ω)) P := by
      apply integrable_finset_sum
      intro i hi
      exact hStepI n i hi
    exact hsum.congr ((hEq n).symm)
  have hFzero (n : ℕ) : (∫ ω, F n ω ∂P) = 0 := by
    rw [integral_congr_ae (hEq n)]
    rw [integral_finset_sum (S n) (fun i hi => hStepI n i hi)]
    apply Finset.sum_eq_zero
    intro i hi
    exact hStepZero n i hi
  have hMm : AEStronglyMeasurable M P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hFI n).aestronglyMeasurable) hConv
  have hMb : ∀ᵐ ω ∂P, |M ω| ≤ K := by
    filter_upwards [hConv, ae_all_iff.mpr hBound] with ω hc hb
    exact le_of_tendsto hc.abs (Eventually.of_forall hb)
  have hMI : Integrable M P := Integrable.of_bound hMm K
    (hMb.mono fun ω hw => by simpa only [Real.norm_eq_abs] using hw)
  have ht := tendsto_integral_of_dominated_convergence
    (fun _ : Ω => K) (fun n => (hFI n).aestronglyMeasurable)
    (integrable_const K)
    (fun n => (hBound n).mono fun ω hw => by
      simpa only [Real.norm_eq_abs] using hw) hConv
  refine ⟨hBridge, hMI, ?_⟩
  exact tendsto_nhds_unique ht (by
    simpa only [hFzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
