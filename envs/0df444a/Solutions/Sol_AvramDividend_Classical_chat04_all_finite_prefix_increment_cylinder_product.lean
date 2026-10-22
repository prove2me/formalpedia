-- Prove2me | solution 1 for AvramDividend.Classical.chat04_all_finite_prefix_increment_cylinder_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:56:27.960225+00:00
-- url     : https://prove2.me/submissions/5e0b0936-aaff-400b-beef-cb03dd33f9fb

import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_finite_increment_prefix_event_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_past_event_next_levy_increment_measure_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The uniform finite-dimensional cylinder measure law. ANY event from
the past F_s and ANY finite prefix n of ordered Lévy increments
factor into P(A) multiplied by all increment-cylinder probabilities.
The induction uses full-filtration independence at each next time,
not the false principle of coordinatewise-independent vectors.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (hst : s ≤ t 0)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (n : ℕ) :
    P (A ∩ {ω | ∀ i : ℕ, i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω ∈ B i}) =
      P A * ∏ i ∈ Finset.range n,
        P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B i} := by
  let C : ℕ → Set Ω :=
    fun i => {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B i}
  let S : ℕ → Set Ω :=
    fun k => {ω | ∀ i : ℕ, i < k → ω ∈ C i}
  have hMain :
      ∀ k : ℕ, P (A ∩ S k) =
        P A * ∏ i ∈ Finset.range k, P (C i) := by
    intro k
    induction k with
    | zero =>
      simp [S]
    | succ k ih =>
      have hS : MeasurableSet[𝓕 (t k)] (S k) := by
        simpa only [S, C, Set.mem_setOf_eq] using
          (AvramDividend.Classical.chat04_finite_increment_prefix_event_filtration_measurable
            X t ht k B hB)
      have hAt : MeasurableSet[𝓕 (t k)] A :=
        (𝓕.mono (hst.trans (ht (Nat.zero_le k)))) A hA
      have hPast : MeasurableSet[𝓕 (t k)] (A ∩ S k) :=
        hAt.inter hS
      have hStep : S (k + 1) = S k ∩ C k := by
        ext ω
        simp only [S, C, Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · intro h
          exact ⟨(fun i hi => h i (Nat.lt_succ_of_lt hi)),
            h k (Nat.lt_succ_self k)⟩
        · rintro ⟨hp, hn⟩ i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
          · exact hp i hlt
          · subst i
            exact hn
      have hFactor : P ((A ∩ S k) ∩ C k) =
          P (A ∩ S k) * P (C k) := by
        simpa only [C] using
          (AvramDividend.Classical.chat04_past_event_next_levy_increment_measure_product
            X (t k) (t (k + 1)) (ht (Nat.le_succ k))
            (A ∩ S k) hPast (B k) (hB k))
      calc
        P (A ∩ S (k + 1)) =
            P ((A ∩ S k) ∩ C k) := by rw [hStep, ← Set.inter_assoc]
        _ = P (A ∩ S k) * P (C k) := hFactor
        _ = P A * ∏ i ∈ Finset.range (k + 1), P (C i) := by
          rw [ih, Finset.prod_range_succ, mul_assoc]
  simpa only [S, C, Set.mem_setOf_eq] using hMain n
