-- Prove2me | solution 1 for CongestionPoA.SymMax.theorem1_sum_le_five_halves
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:12:40.481989+00:00
-- url     : https://prove2.me/submissions/ebcbc879-2dd7-41c7-9c97-fe778472187a

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

set_option autoImplicit false

namespace CongestionPoA.SymMax.P74f3

theorem key_ineq (x y : ℕ) :
    (x : ℝ) * ((y : ℝ) + 1) ≤ 1 / 3 * ((y : ℝ) * y) + 5 / 3 * ((x : ℝ) * x) := by
  have h : (3 * x * (y + 1) : ℤ) ≤ y * y + 5 * x * x := by
    rcases Nat.lt_or_ge x 2 with hx | hx
    · interval_cases x
      · simp; positivity
      · rcases Nat.lt_or_ge y 2 with hy | hy
        · interval_cases y <;> norm_num
        · have : (2 : ℤ) ≤ y := by exact_mod_cast hy
          push_cast
          nlinarith [mul_nonneg (sub_nonneg.mpr this) (by linarith : (0:ℤ) ≤ (y:ℤ) - 1)]
    · have : (2 : ℤ) ≤ x := by exact_mod_cast hx
      nlinarith [sq_nonneg (2 * (y : ℤ) - 3 * x)]
  have h' : ((3 * x * (y + 1) : ℤ) : ℝ) ≤ ((y * y + 5 * x * x : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

theorem sumCost_eq {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A : ι → Finset E) :
    sumCost G A = ∑ e, (load A e : ℝ) * G.latency e (load A e) := by
  unfold sumCost cost
  calc ∑ i, ∑ e ∈ A i, G.latency e (load A e)
      = ∑ i, ∑ e, (if e ∈ A i then G.latency e (load A e) else 0) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_ite_mem]; simp
    _ = ∑ e, ∑ i, (if e ∈ A i then G.latency e (load A e) else 0) := Finset.sum_comm
    _ = ∑ e, (load A e : ℝ) * G.latency e (load A e) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [← Finset.sum_filter]; simp [load]

end CongestionPoA.SymMax.P74f3

namespace CongestionPoA.SymMax.P74f3x

theorem load_update_le {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (A : ι → Finset E) (i : ι) (S : Finset E) (e : E) :
    load (Function.update A i S) e ≤ load A e + 1 := by
  unfold load
  calc (Finset.univ.filter (fun j => e ∈ Function.update A i S j)).card
      ≤ (insert i (Finset.univ.filter (fun j => e ∈ A j))).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [Finset.mem_insert, Finset.mem_filter]
        by_cases hji : j = i
        · exact Or.inl hji
        · right
          refine ⟨Finset.mem_univ _, ?_⟩
          rwa [Function.update_of_ne hji] at hj
    _ ≤ (Finset.univ.filter (fun j => e ∈ A j)).card + 1 := Finset.card_insert_le _ _

theorem swap_sum {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (P : ι → Finset E) (f : E → ℝ) :
    ∑ i, ∑ e ∈ P i, f e = ∑ e, (load P e : ℝ) * f e := by
  calc ∑ i, ∑ e ∈ P i, f e
      = ∑ i, ∑ e, (if e ∈ P i then f e else 0) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_ite_mem]; simp
    _ = ∑ e, ∑ i, (if e ∈ P i then f e else 0) := Finset.sum_comm
    _ = ∑ e, (load P e : ℝ) * f e := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [← Finset.sum_filter]; simp [load]

end CongestionPoA.SymMax.P74f3x

open CongestionPoA.SymMax in
theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ 5 / 2 * sumCost G P := by
  obtain ⟨a, b, ha, hb, hf⟩ := hlin
  have hdev : sumCost G A ≤ ∑ e, (load P e : ℝ) * G.latency e (load A e + 1) := by
    rw [← CongestionPoA.SymMax.P74f3x.swap_sum]
    unfold sumCost
    apply Finset.sum_le_sum
    intro i _
    refine le_trans (hA.2 i (P i) (hP i)) ?_
    unfold cost
    rw [Function.update_self]
    apply Finset.sum_le_sum
    intro e _
    rw [hf, hf]
    have h1 := CongestionPoA.SymMax.P74f3x.load_update_le A i (P i) e
    have h2 : ((load (Function.update A i (P i)) e : ℕ) : ℝ) ≤ ((load A e + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    have := mul_le_mul_of_nonneg_left h2 (ha e)
    linarith
  have hstep : ∑ e, (load P e : ℝ) * G.latency e (load A e + 1) ≤
      1 / 3 * sumCost G A + 5 / 3 * sumCost G P := by
    rw [CongestionPoA.SymMax.P74f3.sumCost_eq, CongestionPoA.SymMax.P74f3.sumCost_eq,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e _
    rw [hf, hf, hf]
    push_cast
    have k := CongestionPoA.SymMax.P74f3.key_ineq (load P e) (load A e)
    have hx : (0 : ℝ) ≤ (load P e : ℝ) := Nat.cast_nonneg _
    have hy : (0 : ℝ) ≤ (load A e : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left k (ha e), mul_nonneg (hb e) hx, mul_nonneg (hb e) hy]
  linarith
