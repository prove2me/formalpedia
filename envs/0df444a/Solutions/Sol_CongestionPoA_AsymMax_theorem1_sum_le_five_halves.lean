-- Prove2me | solution 1 for CongestionPoA.AsymMax.theorem1_sum_le_five_halves
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:18:40.504629+00:00
-- url     : https://prove2.me/submissions/a5681961-8214-41cc-9eb3-48e23758cf65

import Definitions.Def_CongestionPoA_AsymMax_Model
set_option autoImplicit false
open CongestionPoA.AsymMax

theorem dc {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (g : E → ℝ) :
    ∑ i, ∑ e ∈ A i, g e = ∑ e, (load A e : ℝ) * g e := by
  have h : ∀ i, ∑ e ∈ A i, g e = ∑ e, if e ∈ A i then g e else 0 := fun i => by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_filter]
  simp [load, mul_comm]

theorem sumCost_eq {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A : ι → Finset E) :
    sumCost G A = ∑ e, (load A e : ℝ) * G.latency e (load A e) :=
  dc A (fun e => G.latency e (load A e))

theorem load_update_le {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (i : ι) (S : Finset E) (e : E) :
    load (Function.update A i S) e ≤ load A e + 1 := by
  unfold load
  calc (Finset.univ.filter fun j => e ∈ Function.update A i S j).card
      ≤ (insert i (Finset.univ.filter fun j => e ∈ A j)).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        by_cases hji : j = i
        · simp [hji]
        · simp [Function.update_apply, hji] at hj
          simp [hj]
    _ ≤ _ := Finset.card_insert_le _ _

theorem dev_bound {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ)
    (ha : ∀ e, 0 ≤ a e)
    (hlat : ∀ e n, G.latency e n = a e * n + b e)
    (A : ι → Finset E) (hA : IsPureNash G A) (S : Finset E) (i : ι) (hS : S ∈ G.strategies i) :
    cost G A i ≤ ∑ e ∈ S, (a e * ((load A e : ℝ) + 1) + b e) := by
  refine (hA.2 i S hS).trans ?_
  unfold cost
  rw [Function.update_self]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [hlat]
  have h1 := load_update_le A i S e
  have h2 : ((load (Function.update A i S) e : ℕ) : ℝ) ≤ load A e + 1 := by exact_mod_cast h1
  nlinarith [ha e]

theorem poa_ab {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e n, G.latency e n = a e * n + b e)
    (A P : ι → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ (5 / 2 : ℝ) * sumCost G P := by
  have hsum : ∀ B : ι → Finset E, sumCost G B = ∑ e, ((a e * (load B e : ℝ) ^ 2) + b e * load B e) := by
    intro B
    rw [sumCost_eq]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hlat]; ring
  have key : ∀ x y : ℕ, (y : ℝ) * ((x : ℝ) + 1) * 3 ≤ 5 * (y : ℝ) ^ 2 + (x : ℝ) ^ 2 := by
    intro x y
    have hz : (y : ℤ) * ((x : ℤ) + 1) * 3 ≤ 5 * (y : ℤ) ^ 2 + (x : ℤ) ^ 2 := by
      rcases Nat.lt_or_ge y 2 with hy | hy
      · interval_cases y
        · simp
        · rcases Nat.lt_or_ge x 2 with hx | hx
          · interval_cases x <;> norm_num
          · have : (2 : ℤ) ≤ x := by exact_mod_cast hx
            have h : (0 : ℤ) ≤ ((x : ℤ) - 2) * ((x : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
            push_cast
            nlinarith
      · have hy' : (2 : ℤ) ≤ y := by exact_mod_cast hy
        nlinarith [sq_nonneg (2 * (x : ℤ) - 3 * y)]
    exact_mod_cast hz
  have h1 : sumCost G A ≤ ∑ e, (load P e : ℝ) * (a e * ((load A e : ℝ) + 1) + b e) := by
    calc sumCost G A = ∑ i, cost G A i := rfl
      _ ≤ ∑ i, ∑ e ∈ P i, (a e * ((load A e : ℝ) + 1) + b e) :=
          Finset.sum_le_sum fun i _ => dev_bound G a b ha hlat A hA (P i) i (hP i)
      _ = _ := dc P (fun e => a e * ((load A e : ℝ) + 1) + b e)
  have h2 : ∑ e, (load P e : ℝ) * (a e * ((load A e : ℝ) + 1) + b e) * 3 ≤
      ∑ e, (a e * (5 * (load P e : ℝ) ^ 2 + (load A e : ℝ) ^ 2) + 3 * (b e * load P e)) := by
    refine Finset.sum_le_sum fun e _ => ?_
    have := key (load A e) (load P e)
    have := ha e
    nlinarith [mul_le_mul_of_nonneg_left (key (load A e) (load P e)) (ha e)]
  have h3 : ∑ e, (load P e : ℝ) * (a e * ((load A e : ℝ) + 1) + b e) * 3 =
      3 * ∑ e, (load P e : ℝ) * (a e * ((load A e : ℝ) + 1) + b e) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  have h4 : ∑ e, (a e * (5 * (load P e : ℝ) ^ 2 + (load A e : ℝ) ^ 2) + 3 * (b e * load P e)) =
      5 * ∑ e, (a e * (load P e : ℝ) ^ 2) + ∑ e, (a e * (load A e : ℝ) ^ 2) +
        3 * ∑ e, (b e * (load P e : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hP' : sumCost G P = ∑ e, a e * (load P e : ℝ) ^ 2 + ∑ e, b e * (load P e : ℝ) := by
    rw [hsum, ← Finset.sum_add_distrib]
  have hA' : sumCost G A = ∑ e, a e * (load A e : ℝ) ^ 2 + ∑ e, b e * (load A e : ℝ) := by
    rw [hsum, ← Finset.sum_add_distrib]
  have hbA : 0 ≤ ∑ e, b e * (load A e : ℝ) :=
    Finset.sum_nonneg fun e _ => mul_nonneg (hb e) (Nat.cast_nonneg _)
  have hbP : 0 ≤ ∑ e, b e * (load P e : ℝ) :=
    Finset.sum_nonneg fun e _ => mul_nonneg (hb e) (Nat.cast_nonneg _)
  have haP : 0 ≤ ∑ e, a e * (load P e : ℝ) ^ 2 :=
    Finset.sum_nonneg fun e _ => mul_nonneg (ha e) (sq_nonneg _)
  nlinarith

theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ (5 / 2 : ℝ) * sumCost G P := by
  obtain ⟨a, b, ha, hb, hlat⟩ := hlin
  exact poa_ab G a b ha hb hlat A P hA hP

