-- Prove2me | solution 1 for BlockCycleRotation.quadExpansion_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:00:22.52829+00:00
-- url     : https://prove2.me/submissions/fa12cb5c-f09d-40bb-a16e-6db6e63ce339

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_append
import Theorems.Thm_BlockCycleRotation_K_reverse
import Theorems.Thm_BlockCycleRotation_K_cf
import Theorems.Thm_BlockCycleRotation_cf_spec
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

/-- Mirror of the earlier reversal identity. -/
theorem reverse_tail_eq (l : List ℕ) : (l.reverse).tail = (l.dropLast).reverse := by
  have h : ((l.reverse).reverse).dropLast = ((l.reverse).tail).reverse := by
    rcases hl : l.reverse with _ | ⟨a, t⟩ <;> simp
  rw [List.reverse_reverse] at h
  rw [h, List.reverse_reverse]

theorem mem_quadruples {n a b a' b' : ℕ} :
    (a, b, a', b') ∈ quadruples n ↔
      (a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b' ∧ b' < b
        ∧ Nat.gcd a a' = 1 ∧ Nat.gcd b b' = 1 ∧ n = a * b + a' * b' := by
  simp [quadruples, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem head_opt_append_of_ne_nil {l₁ l₂ : List ℕ} (h : l₁ ≠ []) :
    (l₁ ++ l₂).head? = l₁.head? := by
  rcases l₁ with _ | ⟨x, xs⟩
  · exact absurd rfl h
  · simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The expansion attached to a quadruple is the split it came from.**  It is
a normalised expansion of `n`, and splitting it at `|cf a a'|` returns the two
halves. -/
theorem solution {n a b a' b' : ℕ} (hq : (a, b, a', b') ∈ quadruples n) :
    K (quadExpansion a b a' b') = n ∧ quadExpansion a b a' b' ≠ []
      ∧ (∀ c ∈ quadExpansion a b a' b', 1 ≤ c)
      ∧ (∀ x ∈ (quadExpansion a b a' b').head?, 2 ≤ x)
      ∧ (∀ x ∈ (quadExpansion a b a' b').getLast?, 2 ≤ x)
      ∧ (quadExpansion a b a' b').take (cf a a').length = cf a a'
      ∧ (quadExpansion a b a' b').drop (cf a a').length = (cf b b').reverse
      ∧ 1 ≤ (cf a a').length
      ∧ (cf a a').length < (quadExpansion a b a' b').length:= by
  obtain ⟨-, ha1, ha2, hb1, hb2, hga, hgb, hsum⟩ := mem_quadruples.1 hq
  obtain ⟨hKa, hKa'⟩ := K_cf a' a ha1 ha2 hga
  obtain ⟨hnea, hposa, hheada⟩ := cf_spec a' a ha1 ha2 hga
  obtain ⟨hKb, hKb'⟩ := K_cf b' b hb1 hb2 hgb
  obtain ⟨hneb, hposb, hheadb⟩ := cf_spec b' b hb1 hb2 hgb
  have hnebr : (cf b b').reverse ≠ [] := by simpa using hneb
  have hKbr : K (cf b b').reverse = b := by rw [K_reverse]; exact hKb
  have hKbr' : K ((cf b b').reverse).tail = b' := by
    rw [reverse_tail_eq, K_reverse]; exact hKb'
  have hlen : 1 ≤ (cf a a').length := List.length_pos_iff.2 hnea
  refine ⟨?_, ?_, ?_, ?_, ?_, List.take_left, List.drop_left, hlen, ?_⟩
  · rw [quadExpansion, K_append _ _ hnea hnebr, hKa, hKa', hKbr, hKbr', hsum]
  · simp [quadExpansion, hnea]
  · intro c hc
    rcases List.mem_append.1 hc with h | h
    · exact hposa c h
    · exact hposb c (List.mem_reverse.1 h)
  · intro x hx
    rw [quadExpansion, head_opt_append_of_ne_nil hnea] at hx
    exact hheada x hx
  · intro x hx
    rw [quadExpansion, List.getLast?_append_of_ne_nil _ hnebr,
      List.getLast?_reverse] at hx
    exact hheadb x hx
  · rw [quadExpansion, List.length_append]
    have hbl : 0 < (cf b b').reverse.length := List.length_pos_iff.2 hnebr
    omega
