-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise33_original_dyadic_signed_band_L1_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:14:12.13986+00:00
-- url     : https://prove2.me/submissions/87473c03-aedc-41cd-b532-b6d65db8faa7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise35_original_dyadic_finite_simple_condexp
import Theorems.Thm_AvramDividend_Classical_avram_anoise36_original_dyadic_physical_L1_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Assemble the finite-simple original-filtration conditional centring with
physical convergence and an original-space integrable dominator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      ∃ bound : Ω → ℝ, Integrable bound P ∧
        (∀ k, Integrable (M k) P) ∧
        (∀ k, P[M k | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun k => M k ω) atTop
          (𝓝 (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω))) ∧
        (∀ k, ∀ᵐ ω ∂P, ‖M k ω‖ ≤ bound ω) := by
  intro n s t hst
  obtain ⟨hMInt, hMZero⟩ :=
    avram_anoise35_original_dyadic_finite_simple_condexp X hFinite n s t hst
  obtain ⟨bound, hBoundInt, hLim, hBound⟩ :=
    avram_anoise36_original_dyadic_physical_L1_source
      X hFinite hInt n s t hst
  exact ⟨bound, hBoundInt, hMInt, hMZero, hLim, hBound⟩
