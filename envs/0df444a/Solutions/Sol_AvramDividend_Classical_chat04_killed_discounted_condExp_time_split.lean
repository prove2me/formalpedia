-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_discounted_condExp_time_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:37:19.694917+00:00
-- url     : https://prove2.me/submissions/871d6947-6831-4f3c-9d13-309f236f2fcb

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_lower_killed_condExp_markov_factorisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (W : ℝ → ℝ)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u)
    (hInt : Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (s : ℝ))) *
          P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
            0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
              (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
                W (x + X.X u ω)) | 𝓕 s] ω) := by
  let A : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}
  let B : Set Ω := {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
    0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}
  let D : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}
  let a : ℝ := Real.exp (-(q * (s : ℝ)))
  let F : Ω → ℝ :=
    fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) * W (x + X.X u ω)
  have hExp : Real.exp (-(q * (u : ℝ))) =
      a * Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) := by
    dsimp [a]
    rw [← Real.exp_add]
    congr 1
    ring
  have hPayload :
      (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) =
        (fun ω => a * F ω) := by
    funext ω
    dsimp only [F]
    rw [hExp]
    ring
  have hIndicator : B.indicator (fun ω => a * F ω) =
      fun ω => a * B.indicator F ω := by
    funext ω
    by_cases hb : ω ∈ B
    · simp [Set.indicator, hb]
    · simp [Set.indicator, hb]
  have hF : Integrable (B.indicator F) P := hInt
  have hScaled : Integrable (B.indicator (fun ω => a * F ω)) P := by
    rw [hIndicator]
    exact hF.const_mul a
  have hMarkov := AvramDividend.Classical.chat04_lower_killed_condExp_markov_factorisation
    X τ hCover x s u hsu (fun ω => a * F ω) hScaled
  change P[D.indicator (fun ω => a * F ω) | 𝓕 s] =ᵐ[P]
    A.indicator (P[B.indicator (fun ω => a * F ω) | 𝓕 s]) at hMarkov
  have hOne : (fun ω : Ω => a * (B.indicator F) ω) =
      a • B.indicator F := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
  have hTwo : (fun ω : Ω => a * P[B.indicator F | 𝓕 s] ω) =
      a • P[B.indicator F | 𝓕 s] := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
  have hCE :
      P[B.indicator (fun ω => a * F ω) | 𝓕 s] =ᵐ[P]
        fun ω => a * P[B.indicator F | 𝓕 s] ω := by
    rw [hIndicator, hOne, hTwo]
    exact MeasureTheory.condExp_smul (μ := P) a (B.indicator F) (𝓕 s)
  change P[D.indicator
      (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
    A.indicator (fun ω => a * P[B.indicator F | 𝓕 s] ω)
  rw [hPayload]
  filter_upwards [hMarkov, hCE] with ω hm hc
  calc
    _ = A.indicator (P[B.indicator (fun ω => a * F ω) | 𝓕 s]) ω := hm
    _ = A.indicator (fun ω => a * P[B.indicator F | 𝓕 s] ω) ω := by
      by_cases ha : ω ∈ A
      · simpa [Set.indicator, ha] using hc
      · simp [Set.indicator, ha]