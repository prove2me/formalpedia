-- Prove2me | solution 1 for CongestionPoA.AsymMax.inequality1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:18:04.018868+00:00
-- url     : https://prove2.me/submissions/6c90b90b-4864-4935-85b4-ebb27ecbac68

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

theorem load_pos {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (i : ι) (e : E) (h : e ∈ A i) : 1 ≤ load A e := by
  unfold load
  exact Finset.card_pos.mpr ⟨i, by simp [h]⟩

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

theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e n, G.latency e n = a e * n + b e)
    (A P : ι → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P)
    (i : ι) :
    cost G A i ≤ (∑ e ∈ P i, a e * (load A e : ℝ)) + cost G P i := by
  refine (dev_bound G a b ha hlat A hA (P i) i (hP i)).trans ?_
  unfold cost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e he => ?_
  rw [hlat]
  have h1 : (1 : ℝ) ≤ load P e := by exact_mod_cast load_pos P i e he
  nlinarith [ha e]

