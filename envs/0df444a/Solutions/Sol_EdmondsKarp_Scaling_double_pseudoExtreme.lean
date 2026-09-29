-- Prove2me | solution 1 for EdmondsKarp.Scaling.double_pseudoExtreme
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:47:37.583919+00:00
-- url     : https://prove2.me/submissions/8f1b476a-e991-4171-80c2-c7a1f5b7cd56

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run

namespace EdmondsKarp.Scaling

theorem aux_dp_natdiv (a p : ℕ) (hp : 1 ≤ p) : 2 * (a / 2 ^ p) ≤ a / 2 ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le (a / 2 ^ q) 2

theorem aux_dp_realdiv (a p : ℕ) (hp : 1 ≤ p) :
    (2 : ℝ) * ((a / 2 ^ p : ℕ) : ℝ) ≤ ((a / 2 ^ (p - 1) : ℕ) : ℝ) := by
  exact_mod_cast aux_dp_natdiv a p hp

end EdmondsKarp.Scaling

open EdmondsKarp.Scaling

theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (p : ℕ) (hp : 1 ≤ p) (x : Flow m n)
    (hx : IsPseudoExtreme (problem a b d p) x) :
    IsPseudoExtreme (problem a b d (p - 1)) ((2 : ℝ) • x) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, u, v, hu1, hu2⟩ := hx
  have ef0 : ∀ i, ((2 : ℝ) • x).f0 i = 2 * x.f0 i := fun _ => rfl
  have efx : ∀ i j, ((2 : ℝ) • x).fx i j = 2 * x.fx i j := fun _ _ => rfl
  have efz : ∀ j, ((2 : ℝ) • x).fz j = 2 * x.fz j := fun _ => rfl
  have eret : ((2 : ℝ) • x).ret = 2 * x.ret := rfl
  simp only [problem] at h5 h6 hu1 hu2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, u, v, ?_, ?_⟩
  · intro i; rw [ef0]; linarith [h1 i]
  · intro i j; rw [efx]; linarith [h2 i j]
  · intro j; rw [efz]; linarith [h3 j]
  · rw [eret]; linarith
  · intro i; rw [ef0]; simp only [problem]
    linarith [h5 i, aux_dp_realdiv (a i) p hp]
  · intro j; rw [efz]; simp only [problem]
    linarith [h6 j, aux_dp_realdiv (b j) p hp]
  · simp only [ef0, eret, ← Finset.mul_sum]; linarith
  · intro i; simp only [ef0, efx, ← Finset.mul_sum]; linarith [h8 i]
  · intro j; simp only [efz, efx, ← Finset.mul_sum]; linarith [h9 j]
  · simp only [efz, eret, ← Finset.mul_sum]; linarith
  · intro i j; simp only [problem]; exact hu1 i j
  · intro i j h; simp only [problem] at h; rw [efx, hu2 i j h]; ring
