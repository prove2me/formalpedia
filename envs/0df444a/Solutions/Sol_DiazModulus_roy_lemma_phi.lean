-- Prove2me | solution 1 for DiazModulus.roy_lemma_phi
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:13:11.896235+00:00
-- url     : https://prove2.me/submissions/bf7c605b-e536-4a58-a3e2-2133c7c96a5d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_phi_closed_form_superadd

open Complex ComplexConjugate

/-! # Roy's Lemma (Roy 1992, p. 40)

For `0 < n < d`, a decomposition of `(n, d)` is a list of pairs `(nᵢ, dᵢ)` with `0 < nᵢ < dᵢ`, `Σnᵢ = n`,
`Σdᵢ = d`, and its value is `Σ nᵢdᵢ/(dᵢ − nᵢ)`. Let `F(n, d)` be `nd/(d − n)` if `n = 1` or `d − n = 1`, and
`(d − n)/(d − n − 1) + (n − 1)n` otherwise. The largest value is `F(n, d)`.
Upper bound: by induction on a non-empty decomposition, its sums satisfy `0 < Σnᵢ < Σdᵢ` and its value is at most
`F(Σnᵢ, Σdᵢ)`. A single part has value at most `F` of that part; for a part `(a, x)` followed by a non-empty tail
with sums `(n', d')`, the value is at most `F(a, x) + F(n', d') ≤ F(a + n', x + d')`, since the closed form is
superadditive. Attained: if `n = 1` or `d − n = 1` the one-part decomposition `[(n, d)]` has value `nd/(d − n)`;
otherwise `[(1, d − n), (n − 1, n)]` is a decomposition with value `(d − n)/(d − n − 1) + (n − 1)n`. -/

namespace RC4_R1
open DiazModulus

/-- The closed form of Roy's maximum (same formula as the statement). -/
def Fq (n d : ℕ) : ℚ :=
  if n = 1 ∨ d - n = 1 then ((n : ℚ) * d) / ((d : ℚ) - n)
  else ((d : ℚ) - n) / ((d : ℚ) - n - 1) + ((n : ℚ) - 1) * n

theorem closed_form :
    (∀ a x : ℕ, 0 < a → a < x → ((a : ℚ) * x) / ((x : ℚ) - a) ≤ Fq a x) ∧
    ∀ a x b y : ℕ, 0 < a → a < x → 0 < b → b < y → Fq a x + Fq b y ≤ Fq (a + b) (x + y) :=
  DiazModulus.roy_phi_closed_form_superadd

/-- A non-empty decomposition: its sums satisfy `0 < Σ fst < Σ snd`, and its value is at most `Fq`. -/
theorem bound (D : List (ℕ × ℕ)) (hD : ∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) (hne : D ≠ []) :
    0 < (D.map Prod.fst).sum ∧ (D.map Prod.fst).sum < (D.map Prod.snd).sum ∧
    (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum ≤
      Fq (D.map Prod.fst).sum (D.map Prod.snd).sum := by
  induction D with
  | nil => exact absurd rfl hne
  | cons p D ih =>
    have hp := hD p List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    by_cases hD' : D = []
    · subst hD'
      simp only [List.map_nil, List.sum_nil, add_zero]
      exact ⟨hp.1, hp.2, closed_form.1 _ _ hp.1 hp.2⟩
    · obtain ⟨h1, h2, h3⟩ := ih (fun q hq => hD q (List.mem_cons_of_mem _ hq)) hD'
      refine ⟨by omega, by omega, ?_⟩
      have := closed_form.1 _ _ hp.1 hp.2
      have := closed_form.2 _ _ _ _ hp.1 hp.2 h1 h2
      linarith

/-- The closed form is the value of an explicit decomposition. -/
theorem attained {n d : ℕ} (hn : 0 < n) (hnd : n < d) :
    ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
      (D.map Prod.fst).sum = n ∧ (D.map Prod.snd).sum = d ∧
      Fq n d = (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  by_cases h : n = 1 ∨ d - n = 1
  · refine ⟨[(n, d)], ?_, by simp, by simp, ?_⟩
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact ⟨hn, hnd⟩
    · simp only [Fq, if_pos h, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  · refine ⟨[(1, d - n), (n - 1, n)], ?_, ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨one_pos, by omega⟩
      · exact ⟨by omega, by omega⟩
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · simp only [Fq, if_neg h, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [Nat.cast_sub hnd.le, Nat.cast_sub hn]
      push_cast
      rw [show (n : ℚ) - (n - 1) = 1 by ring, div_one]
      ring

end RC4_R1

open DiazModulus RC4_R1 in
theorem solution {n d : ℕ} (hn : 0 < n) (hnd : n < d) :
    IsGreatest
      {x : ℚ | ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
        (D.map Prod.fst).sum = n ∧ (D.map Prod.snd).sum = d ∧
        x = (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum}
      (if n = 1 ∨ d - n = 1 then ((n : ℚ) * d) / ((d : ℚ) - n)
        else ((d : ℚ) - n) / ((d : ℚ) - n - 1) + ((n : ℚ) - 1) * n) := by
  show IsGreatest _ (Fq n d)
  constructor
  · exact attained hn hnd
  · rintro x ⟨D, hD, h1, h2, rfl⟩
    have hne : D ≠ [] := by
      rintro rfl
      simp only [List.map_nil, List.sum_nil] at h1
      omega
    have := (bound D hD hne).2.2
    rwa [h1, h2] at this
