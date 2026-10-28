-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_esscher_scaled_renewal_kernel_series_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:25:50.103209+00:00
-- url     : https://prove2.me/submissions/cc92c494-4122-4d3f-86ee-af15b6c16ff3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_renewal_kernel_series_data
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧
      0 < ρ ∧ ρ < 1 ∧
      Integrable κ volume ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M) ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) ∧
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => b * ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x =
          c + ∫ y in (0 : ℝ)..x,
            (b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y)) := by
  obtain ⟨φ, c, ρ, κ, F, hφ, hroot, hρ, hρlt, hκintegrable,
      hκcont, hκzero, hκbounded, hFzero, hFsucc, hFpos,
      hFbound, hInterval, hRepresentation⟩ :=
    bv_ac_esscher_renewal_kernel_series_data X hX q hq W hW hbv hac
  refine ⟨φ, c, ρ, 1, κ, F, hφ, hroot, hρ, hρlt,
    hκintegrable, hκcont, hκzero, hκbounded, hFzero, hFsucc,
    hFpos, hFbound, ?_, ?_⟩
  · intro x hx
    simpa only [one_mul] using hInterval x hx
  · intro x hx
    simpa only [one_mul] using hRepresentation x hx
