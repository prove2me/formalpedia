-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_pairwise_L2_tail_energy_to_centered_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:13:25.393041+00:00
-- url     : https://prove2.me/submissions/a02ed6b8-6bd9-4bdb-80f1-2493f0ca9727

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Vanishing earlier-band quadratic energy controls every later original
intrinsic compensated jump approximation and its centred L² limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (clock : Measure ℝ≥0)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (B : ℕ → Set ((ℝ≥0 × Ω) × ℝ))
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hRep : ∀ n, (M n : Ω → ℝ) =ᵐ[P] fun ω =>
      (∫ p, (B n).indicator G ((p.1, ω), p.2) ∂(NX ω)) -
        ∫ t, ∫ z, (B n).indicator G ((t, ω), z) ∂X.ν ∂clock)
    (E : ℕ → ℝ)
    (hEnergySmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m, N ≤ m → E m < ε ^ 2)
    (hPairwise : ∀ m n, m ≤ n →
      (dist (M m) (M n)) ^ 2 ≤ E m)
    (hCentered : ∀ k, (∫ ω, M k ω ∂P) = 0) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by
  have hCauchy : CauchySeq M := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hEnergySmall ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    rcases le_total m n with hmn | hnm
    · have hSq := hPairwise m n hmn
      have hSmall := hN m hm
      have hNonneg : 0 ≤ dist (M m) (M n) := dist_nonneg
      nlinarith
    · have hSq := hPairwise n m hnm
      have hSmall := hN n hn
      have hNonneg : 0 ≤ dist (M n) (M m) := dist_nonneg
      rw [dist_comm] at hSq hNonneg
      nlinarith
  exact avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
    X M hCauchy hCentered
