-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_canonical_positive_clock_clipped_jump_centered_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:35:57.278465+00:00
-- url     : https://prove2.me/submissions/86084771-c879-47ad-8bed-0e8e308b73b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_sigma_family_clipped_smallmark_L2_centered
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_centered_integral_of_zero_complement
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (sigmaSeq : ℕ → Ω → ℝ≥0)
    (hSigmaStop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (sigmaSeq k ω : WithTop ℝ≥0)))
    (j k n : ℕ) (hA : MeasurableSet {ω : Ω | sigmaSeq k ω ≠ 0}) :
    let τ : Ω → ℝ≥0 := sigmaSeq k
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 ∧
    (∀ ω, τ ω = 0 → ∑ i ∈ Finset.range n, Z i ω = 0) ∧
    (∫ ω in {ω : Ω | sigmaSeq k ω ≠ 0}, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by
  intro τ grid N r H Z
  obtain ⟨hLp, hMean, hZero⟩ :=
    avram_jump6_B_original_canonical_sigma_family_clipped_smallmark_L2_centered
      X x D hD w q K hK cut sigmaSeq hSigmaStop j k n
  refine ⟨hLp, hMean, hZero, ?_⟩
  exact avram_p4_f4_positive_clock_centered_integral_of_zero_complement
    {ω : Ω | sigmaSeq k ω ≠ 0} hA
    (fun ω => ∑ i ∈ Finset.range n, Z i ω) hMean
    (by
      filter_upwards [] with ω
      intro hnot
      exact hZero ω (by simpa using hnot))
