-- Prove2me | solution 1 for FreedmanTail.Laplace.S_le_add_one_of_le_tau
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:32:22.160972+00:00
-- url     : https://prove2.me/submissions/dbf94b62-71a6-418d-bdfa-54967de8912d

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_PartialSums
import Definitions.Def_FreedmanTail_Laplace_CrossingTime

open MeasureTheory ProbabilityTheory


namespace FreedmanTail.Laplace

lemma S_succ_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    FreedmanTail.Bernstein.S X (k + 1) ω = FreedmanTail.Bernstein.S X k ω + X (k + 1) ω := by
  unfold FreedmanTail.Bernstein.S
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma S_lt_of_lt_tau {Ω : Type*} (a : ℝ) (X : ℕ → Ω → ℝ) (ω : Ω) (k : ℕ)
    (hk : (k : WithTop ℕ) < tau a X ω) : FreedmanTail.Bernstein.S X k ω < a := by
  classical
  unfold tau at hk
  split_ifs at hk with h
  · have hk' : k < Nat.find h := by exact_mod_cast hk
    have := Nat.find_min h hk'
    push_neg at this
    exact this
  · by_contra hcon
    push_neg at hcon
    exact h ⟨k, hcon⟩

theorem S_le_add_one_of_le_tau_core {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (a : ℝ) (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, (n : WithTop ℕ) ≤ tau a X ω → FreedmanTail.Bernstein.S X n ω ≤ a + 1 := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, |X (n + 1) ω| ≤ 1 := by
    rw [ae_all_iff]
    intro n
    exact hX_bdd (n + 1) (by omega)
  filter_upwards [hall] with ω hω
  intro n hn
  cases n with
  | zero =>
    simp [FreedmanTail.Bernstein.S]
    linarith
  | succ k =>
    have hk : (k : WithTop ℕ) < tau a X ω := by
      calc (k : WithTop ℕ) < ((k + 1 : ℕ) : WithTop ℕ) := by exact_mod_cast Nat.lt_succ_self k
        _ ≤ tau a X ω := hn
    have h1 := S_lt_of_lt_tau a X ω k hk
    have h2 := hω k
    rw [S_succ_eq]
    have := (abs_le.mp h2).2
    linarith

end FreedmanTail.Laplace

open FreedmanTail.Laplace


theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (a : ℝ) (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, (n : WithTop ℕ) ≤ tau a X ω → FreedmanTail.Bernstein.S X n ω ≤ a + 1 := by
  exact S_le_add_one_of_le_tau_core P ℱ X hX_meas hX_bdd hX_mart a ha
