-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_discounted_clipped_prejump_stopped_fullcutoff_diagonal_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:36:31.993895+00:00
-- url     : https://prove2.me/submissions/aa99e3e5-5cb4-4087-b3b4-723dfa85b261

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_stopped_predictable_full_cutoff_grid_diagonal_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Exact stopped original full-cutoff physical Lévy martingale grid with an actual
controlled pre-jump discounted clipped derivative of w. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (n : ℕ) :
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
    Integrable (fun ω => ∑ i ∈ Finset.range n, (Z i ω)^2) P ∧
      (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range n,
          r i * ∫ ω, (if (τ ω : WithTop ℝ≥0) ≤
            (grid i : WithTop ℝ≥0) then (0 : ℝ)
            else H i ω)^2 ∂P := by
  classical
  let R : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(q * (t : ℝ))) * deriv w (R t ω)
  have hR : IsStronglyPredictable 𝓕.rightCont R := by
    simpa only [R] using
      (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD)
  have hG : IsStronglyPredictable 𝓕.rightCont G := by
    simpa only [G] using
      (avram_wave3_04_discounted_deriv_stronglyPredictable R hR w q)
  have hClip :=
    avram_wave3_04_clipped_stronglyPredictable_bounded G hG K hK
  let H : ℕ → Ω → ℝ := fun i ω => max (-K) (min K (G (grid i) ω))
  have hH (i : ℕ) :
      StronglyMeasurable[𝓕.rightCont (grid i)] (H i) := by
    exact hClip.1.stronglyAdapted (grid i)
  have hBound (i : ℕ) (ω : Ω) : |H i ω| ≤ K := by
    simpa only [H, Real.norm_eq_abs] using hClip.2 (grid i) ω
  simpa only [R, G, H] using
    (avram_jump_phys13_original_stopped_predictable_full_cutoff_grid_diagonal_energy
      X cut τ hτstop grid hGrid H hH K hBound n)
