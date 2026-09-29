-- Prove2me | solution 1 for EdmondsKarp.Scaling.maxFlow_value_problem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:04:13.768504+00:00
-- url     : https://prove2.me/submissions/a6928987-55df-4bdf-9106-2d9bc6542749

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run

namespace EdmondsKarp.Scaling

theorem aux_mfvp_upper {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ)
    (p : ℕ) (y : Flow m n) (hy : IsFlow (problem a b d p) y) :
    y.ret ≤ ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℝ) := by
  obtain ⟨_, _, _, _, ha, hb, hs, _, _, ht⟩ := hy
  rw [Nat.cast_min, Nat.cast_sum, Nat.cast_sum]
  apply le_min
  · have h1 : y.ret = ∑ i, y.f0 i := by linarith
    rw [h1]
    exact Finset.sum_le_sum (fun i _ => ha i)
  · have h1 : y.ret = ∑ j, y.fz j := by linarith
    rw [h1]
    exact Finset.sum_le_sum (fun j _ => hb j)

theorem aux_mfvp_exists {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ)
    (p : ℕ) :
    ∃ x : Flow m n, IsFlow (problem a b d p) x ∧
      x.ret = ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℝ) := by
  have hα0 : ∀ i, (0 : ℝ) ≤ ((a i / 2 ^ p : ℕ) : ℝ) := fun i => Nat.cast_nonneg _
  have hβ0 : ∀ j, (0 : ℝ) ≤ ((b j / 2 ^ p : ℕ) : ℝ) := fun j => Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ ∑ i, ((a i / 2 ^ p : ℕ) : ℝ) := Finset.sum_nonneg (fun i _ => hα0 i)
  have hB0 : (0 : ℝ) ≤ ∑ j, ((b j / 2 ^ p : ℕ) : ℝ) := Finset.sum_nonneg (fun j _ => hβ0 j)
  generalize hαdef : (fun i => ((a i / 2 ^ p : ℕ) : ℝ)) = α at *
  have hαi : ∀ i, ((a i / 2 ^ p : ℕ) : ℝ) = α i := fun i => by rw [← hαdef]
  generalize hβdef : (fun j => ((b j / 2 ^ p : ℕ) : ℝ)) = β at *
  have hβi : ∀ j, ((b j / 2 ^ p : ℕ) : ℝ) = β j := fun j => by rw [← hβdef]
  simp only [hαi, hβi] at hα0 hβ0 hA0 hB0
  generalize hAdef : ∑ i, α i = A at *
  generalize hBdef : ∑ j, β j = B at *
  have hD0 : 0 ≤ max A B := le_max_of_le_left hA0
  refine ⟨⟨fun i => α i * B / max A B, fun i j => α i * β j / max A B,
    fun j => β j * A / max A B, A * B / max A B⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have := hα0 i
      dsimp only
      positivity
    · intro i j
      have := hα0 i
      have := hβ0 j
      dsimp only
      positivity
    · intro j
      have := hβ0 j
      dsimp only
      positivity
    · dsimp only
      positivity
    · intro i
      show α i * B / max A B ≤ ((a i / 2 ^ p : ℕ) : ℝ)
      rw [hαi, mul_div_assoc]
      exact mul_le_of_le_one_right (hα0 i) (div_le_one_of_le₀ (le_max_right A B) hD0)
    · intro j
      show β j * A / max A B ≤ ((b j / 2 ^ p : ℕ) : ℝ)
      rw [hβi, mul_div_assoc]
      exact mul_le_of_le_one_right (hβ0 j) (div_le_one_of_le₀ (le_max_left A B) hD0)
    · show ∑ i, α i * B / max A B - A * B / max A B = 0
      rw [← Finset.sum_div, ← Finset.sum_mul, hAdef, sub_self]
    · intro i
      show ∑ j, α i * β j / max A B - α i * B / max A B = 0
      rw [← Finset.sum_div, ← Finset.mul_sum, hBdef, sub_self]
    · intro j
      show β j * A / max A B - ∑ i, α i * β j / max A B = 0
      rw [← Finset.sum_div, ← Finset.sum_mul, hAdef, mul_comm, sub_self]
    · show A * B / max A B - ∑ j, β j * A / max A B = 0
      rw [← Finset.sum_div, ← Finset.sum_mul, hBdef, mul_comm, sub_self]
  · show A * B / max A B = _
    rw [Nat.cast_min, Nat.cast_sum, Nat.cast_sum]
    simp only [hαi, hβi, hAdef, hBdef]
    rcases eq_or_lt_of_le hD0 with h | h
    · have hA : A = 0 := le_antisymm (h ▸ le_max_left A B) hA0
      have hB : B = 0 := le_antisymm (h ▸ le_max_right A B) hB0
      simp [hA, hB]
    · rw [div_eq_iff h.ne', min_mul_max]

end EdmondsKarp.Scaling

open EdmondsKarp.Scaling

theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ)
    (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (p : ℕ) :
    (∃ x : Flow m n, IsMaxFlow (problem a b d p) x) ∧
      ∀ x : Flow m n, IsMaxFlow (problem a b d p) x →
        x.ret = ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℝ) := by
  obtain ⟨x0, hx0, hret⟩ := aux_mfvp_exists a b d p
  refine ⟨⟨x0, hx0, fun y hy => hret ▸ aux_mfvp_upper a b d p y hy⟩, ?_⟩
  intro x hx
  apply le_antisymm (aux_mfvp_upper a b d p x hx.1)
  rw [← hret]
  exact hx.2 x0 hx0
