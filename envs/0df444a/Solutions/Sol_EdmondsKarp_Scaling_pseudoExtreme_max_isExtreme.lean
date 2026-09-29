-- Prove2me | solution 1 for EdmondsKarp.Scaling.pseudoExtreme_max_isExtreme
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:44:02.45141+00:00
-- url     : https://prove2.me/submissions/c485d025-b198-4837-8b62-995e503ad4eb

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport

namespace EdmondsKarp.Scaling

/-- The proportional flow `f_{ij} = a_i b_j / S` has value `S = ∑ a_i`. -/
theorem aux_pemx_prop_flow {m n : ℕ} (hm : 1 ≤ m) (T : Transport m n)
    (ha : ∀ i, 0 < T.a i) (hb : ∀ j, 0 < T.b j) (hsum : ∑ i, T.a i = ∑ j, T.b j) :
    IsFlow T ⟨T.a, fun i j => T.a i * T.b j / ∑ i, T.a i, T.b, ∑ i, T.a i⟩ := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hS : 0 < ∑ i, T.a i := Finset.sum_pos (fun i _ => ha i) hne
  have hS' : (∑ i, T.a i) ≠ 0 := hS.ne'
  refine ⟨fun i => (ha i).le, fun i j => ?_, fun j => (hb j).le, hS.le, fun i => le_rfl,
    fun j => le_rfl, by simp, fun i => ?_, fun j => ?_, by simp [hsum]⟩
  · exact div_nonneg (mul_nonneg (ha i).le (hb j).le) hS.le
  · simp only
    rw [← Finset.sum_div, ← Finset.mul_sum, ← hsum, mul_div_assoc, div_self hS', mul_one, sub_self]
  · simp only
    rw [← Finset.sum_div, ← Finset.sum_mul, mul_comm, mul_div_assoc, div_self hS',
      mul_one, sub_self]

/-- A flow of value at least `S = ∑ a_i = ∑ b_j` saturates every `a_i` and every `b_j`. -/
theorem aux_pemx_saturate {m n : ℕ} (T : Transport m n) (hsum : ∑ i, T.a i = ∑ j, T.b j)
    (y : Flow m n) (hy : IsFlow T y) (hret : ∑ i, T.a i ≤ y.ret) :
    (∀ i, y.f0 i = T.a i) ∧ (∀ j, y.fz j = T.b j) := by
  obtain ⟨_, _, _, _, hfa, hfb, hs, _, _, ht⟩ := hy
  constructor
  · have hle : ∀ i ∈ (Finset.univ : Finset (Fin m)), y.f0 i ≤ T.a i := fun i _ => hfa i
    have heq : ∑ i, y.f0 i = ∑ i, T.a i := by
      apply le_antisymm (Finset.sum_le_sum hle)
      linarith
    intro i
    exact (Finset.sum_eq_sum_iff_of_le hle).1 heq i (Finset.mem_univ _)
  · have hle : ∀ j ∈ (Finset.univ : Finset (Fin n)), y.fz j ≤ T.b j := fun j _ => hfb j
    have heq : ∑ j, y.fz j = ∑ j, T.b j := by
      apply le_antisymm (Finset.sum_le_sum hle)
      linarith
    intro j
    exact (Finset.sum_eq_sum_iff_of_le hle).1 heq j (Finset.mem_univ _)

theorem aux_pemx_potential {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ) (w : Fin m → Fin n → ℝ) :
    ∑ i, ∑ j, (u i - v j) * w i j = ∑ i, u i * (∑ j, w i j) - ∑ j, v j * (∑ i, w i j) := by
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => v j * w i j)]

end EdmondsKarp.Scaling

open EdmondsKarp.Scaling

theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (T : Transport m n)
    (ha : ∀ i, 0 < T.a i) (hb : ∀ j, 0 < T.b j) (hsum : ∑ i, T.a i = ∑ j, T.b j)
    (hd : ∀ i j, 0 ≤ T.d i j) (x : Flow m n) (hmax : IsMaxFlow T x)
    (hpe : IsPseudoExtreme T x) :
    IsExtreme T x := by
  obtain ⟨hx, hxmax⟩ := hmax
  obtain ⟨-, u, v, h5a, h5b⟩ := hpe
  have hxS : ∑ i, T.a i ≤ x.ret := hxmax _ (aux_pemx_prop_flow hm T ha hb hsum)
  obtain ⟨hxa, hxb⟩ := aux_pemx_saturate T hsum x hx hxS
  refine ⟨hx, fun y hy hyret => ?_⟩
  obtain ⟨hya, hyb⟩ := aux_pemx_saturate T hsum y hy (hyret ▸ hxS)
  have hxrow : ∀ i, ∑ j, x.fx i j = T.a i := fun i => by
    have := hx.2.2.2.2.2.2.2.1 i; rw [← hxa i]; linarith
  have hyrow : ∀ i, ∑ j, y.fx i j = T.a i := fun i => by
    have := hy.2.2.2.2.2.2.2.1 i; rw [← hya i]; linarith
  have hxcol : ∀ j, ∑ i, x.fx i j = T.b j := fun j => by
    have := hx.2.2.2.2.2.2.2.2.1 j; rw [← hxb j]; linarith
  have hycol : ∀ j, ∑ i, y.fx i j = T.b j := fun j => by
    have := hy.2.2.2.2.2.2.2.2.1 j; rw [← hyb j]; linarith
  -- reduced-cost decomposition
  have key : ∀ w : Fin m → Fin n → ℝ,
      ∑ i, ∑ j, (u i - v j + T.d i j) * w i j
        = ∑ i, u i * (∑ j, w i j) - ∑ j, v j * (∑ i, w i j) + ∑ i, ∑ j, T.d i j * w i j := by
    intro w
    rw [← aux_pemx_potential u v w, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hx0 : ∑ i, ∑ j, (u i - v j + T.d i j) * x.fx i j = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rcases (h5a i j).lt_or_eq with h | h
    · rw [h5b i j h, mul_zero]
    · rw [← h, zero_mul]
  have hy0 : 0 ≤ ∑ i, ∑ j, (u i - v j + T.d i j) * y.fx i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (h5a i j) (hy.2.1 i j)
  have kx := key x.fx
  have ky := key y.fx
  simp only [hxrow, hxcol] at kx
  simp only [hyrow, hycol] at ky
  unfold cost
  linarith
