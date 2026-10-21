-- Prove2me | solution 1 for FiniteTD.Markov.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:13:35.85493+00:00
-- url     : https://prove2.me/submissions/2b83f180-673b-4d3e-a3bb-79aa399d7217

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain

set_option autoImplicit false
open FiniteTD.Markov

theorem ftd_key {S : Type} [Fintype S] [DecidableEq S]
    (P : S → S → ℝ) (π : S → ℝ) (m ρ : ℝ)
    (hπ : IsStationaryDist P π) (hA1 : Assumption1 P π m ρ) (τ : ℕ) (V : ℝ)
    (I : S → S → ℝ) (hI : ∀ s u, |I s u| ≤ V) :
    |(∑ s : S, ∑ u : S, π s * (Matrix.of P ^ τ) s u * I s u) -
      (∑ s : S, ∑ u : S, π s * π u * I s u)| ≤ 2 * V * (m * ρ ^ τ) := by
  have hV : 0 ≤ V := by
    by_contra hneg
    have hS : IsEmpty S := by
      by_contra hne
      rw [not_isEmpty_iff] at hne
      obtain ⟨s⟩ := hne
      have := (abs_nonneg (I s s)).trans (hI s s)
      exact hneg this
    have h1 := hπ.2.1
    simp at h1
  have hτ : ∀ s, ∑ u, |(Matrix.of P ^ τ) s u - π u| ≤ 2 * (m * ρ ^ τ) := by
    intro s
    have h := hA1.2.2.2 τ s
    unfold tvDist at h
    linarith
  calc |(∑ s : S, ∑ u : S, π s * (Matrix.of P ^ τ) s u * I s u) -
      (∑ s : S, ∑ u : S, π s * π u * I s u)|
      = |∑ s : S, ∑ u : S, π s * ((Matrix.of P ^ τ) s u - π u) * I s u| := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring
    _ ≤ ∑ s : S, |∑ u : S, π s * ((Matrix.of P ^ τ) s u - π u) * I s u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : S, π s * (2 * V * (m * ρ ^ τ)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        calc |∑ u : S, π s * ((Matrix.of P ^ τ) s u - π u) * I s u|
            ≤ ∑ u : S, |π s * ((Matrix.of P ^ τ) s u - π u) * I s u| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ u : S, π s * V * |(Matrix.of P ^ τ) s u - π u| := by
              refine Finset.sum_le_sum fun u _ => ?_
              rw [abs_mul, abs_mul, abs_of_nonneg (hπ.1 s)]
              have h1 := hI s u
              have h2 := abs_nonneg ((Matrix.of P ^ τ) s u - π u)
              have h3 := hπ.1 s
              nlinarith [mul_nonneg h3 h2, abs_nonneg (I s u)]
          _ = π s * V * ∑ u, |(Matrix.of P ^ τ) s u - π u| := by rw [Finset.mul_sum]
          _ ≤ π s * V * (2 * (m * ρ ^ τ)) :=
              mul_le_mul_of_nonneg_left (hτ s) (mul_nonneg (hπ.1 s) hV)
          _ = π s * (2 * V * (m * ρ ^ τ)) := by ring
    _ = 2 * V * (m * ρ ^ τ) := by rw [← Finset.sum_mul, hπ.2.1, one_mul]

theorem solution {S A B : Type} [Fintype S] [DecidableEq S]
    [MeasurableSpace A] [MeasurableSpace B]
    (P : S → S → ℝ) (π : S → ℝ) (m ρ : ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hA1 : Assumption1 P π m ρ)
    (t τ : ℕ) (hτ : 0 < τ)
    (KX : S → MeasureTheory.Measure A) (KY : S → MeasureTheory.Measure B)
    (hKX : ∀ s, MeasureTheory.IsProbabilityMeasure (KX s))
    (hKY : ∀ u, MeasureTheory.IsProbabilityMeasure (KY u))
    (v : A → B → ℝ) (V : ℝ)
    (hvm : Measurable (fun p : A × B => v p.1 p.2))
    (hv : ∀ a b, |v a b| ≤ V) :
    |(∑ s : S, ∑ u : S, π s * (Matrix.of P ^ τ) s u *
        (∫ a, (∫ b, v a b ∂(KY u)) ∂(KX s))) -
      (∑ s : S, ∑ u : S, π s * π u *
        (∫ a, (∫ b, v a b ∂(KY u)) ∂(KX s)))|
      ≤ 2 * V * (m * ρ ^ τ) := by
  refine ftd_key P π m ρ hπ hA1 τ V (fun s u => ∫ a, (∫ b, v a b ∂(KY u)) ∂(KX s)) ?_
  intro s u
  haveI := hKX s
  haveI := hKY u
  have hin : ∀ a, ‖∫ b, v a b ∂(KY u)‖ ≤ V := fun a => by
    have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := KY u) (f := fun b => v a b)
      (C := V) (Filter.Eventually.of_forall fun b => by simpa [Real.norm_eq_abs] using hv a b)
    simpa using this
  have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := KX s)
    (f := fun a => ∫ b, v a b ∂(KY u)) (C := V) (Filter.Eventually.of_forall hin)
  simpa [Real.norm_eq_abs] using this
