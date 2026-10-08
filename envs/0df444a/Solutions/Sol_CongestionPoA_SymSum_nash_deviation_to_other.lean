-- Prove2me | solution 1 for CongestionPoA.SymSum.nash_deviation_to_other
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T19:38:24.292071+00:00
-- url     : https://prove2.me/submissions/ae9fb99c-836a-4f00-b94f-f6bf4dfe05c3

import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model



namespace CongestionPoA.SymSum

open Finset CongestionPoA.AsymSum

theorem ss_load_eq {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (e : E) :
    (load A e : ℝ) = ∑ j, if e ∈ A j then (1:ℝ) else 0 := by
  unfold load
  rw [Finset.card_filter]; push_cast; rfl

theorem ss_load_update {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (i : ι) (S : Finset E) (e : E) (he : e ∈ S) :
    (load (Function.update A i S) e : ℝ) = load A e + if e ∈ A i then 0 else 1 := by
  rw [ss_load_eq, ss_load_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ j ∈ univ.erase i, (if e ∈ Function.update A i S j then (1:ℝ) else 0)
      = ∑ j ∈ univ.erase i, (if e ∈ A j then (1:ℝ) else 0) :=
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this, Function.update_self]
  by_cases h : e ∈ A i <;> simp [h, he] <;> ring

theorem ss_dev_cost' {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ) (hlin : ∀ e k, G.latency e k = a e * k + b e)
    (A : ι → Finset E) (i : ι) (S : Finset E) :
    cost G (Function.update A i S) i
      = ∑ e ∈ S, (a e * ((load A e : ℝ) + if e ∈ A i then 0 else 1) + b e) := by
  unfold cost
  rw [Function.update_self]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [hlin, ss_load_update A i S e he]

theorem ss_dev_cost {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ) (hlin : ∀ e k, G.latency e k = a e * k + b e)
    (A : ι → Finset E) (i : ι) (S : Finset E) :
    cost G (Function.update A i S) i
      = ∑ e ∈ S, (a e * (load A e : ℝ) + b e) + ∑ e ∈ S \ A i, a e := by
  rw [ss_dev_cost' G a b hlin, Finset.sdiff_eq_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  split_ifs <;> ring

theorem ss_sumcost {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (f : E → ℝ) :
    ∑ i, ∑ e ∈ A i, f e = ∑ e, (load A e : ℝ) * f e := by
  have : ∀ i, ∑ e ∈ A i, f e = ∑ e, if e ∈ A i then f e else 0 := fun i => by
    rw [← Finset.sum_filter]; congr 1; ext; simp
  simp_rw [this]
  rw [Finset.sum_comm]
  congr 1; ext e
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem nd_core {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionGame (Fin N) E) (a b : E → ℝ)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P) (i j : Fin N) :
    cost G A i ≤ ∑ e ∈ P j, (a e * (load A e : ℝ) + b e) + ∑ e ∈ P j \ A i, a e := by
  have hmem : P j ∈ G.strategies i := by rw [hsym i j]; exact hP j
  have := hA.2 i (P j) hmem
  rwa [ss_dev_cost G a b hlin] at this

theorem sj_core {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionGame (Fin N) E) (a b : E → ℝ)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P) (i : Fin N) :
    (N : ℝ) * cost G A i ≤
      ∑ e, (load P e : ℝ) * (a e * (load A e : ℝ) + b e) + ∑ e, a e * (load P e : ℝ)
        - ∑ e ∈ A i, a e * (load P e : ℝ) := by
  have h1 : (N:ℝ) * cost G A i = ∑ _j : Fin N, cost G A i := by simp
  have h2 : ∑ _j : Fin N, cost G A i ≤ ∑ j : Fin N, (∑ e ∈ P j, (a e * (load A e : ℝ) + b e)
      + ∑ e ∈ P j \ A i, a e) :=
    Finset.sum_le_sum (fun j _ => nd_core G a b hlin hsym A P hA hP i j)
  have h3 : ∀ j, ∑ e ∈ P j \ A i, a e
      = ∑ e ∈ P j, a e - ∑ e ∈ P j, (if e ∈ A i then a e else 0) := by
    intro j
    rw [Finset.sdiff_eq_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    split_ifs <;> simp_all
  simp_rw [h3] at h2
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ss_sumcost, ss_sumcost, ss_sumcost] at h2
  have h4 : ∑ e, (load P e : ℝ) * (if e ∈ A i then a e else 0)
      = ∑ e ∈ A i, a e * (load P e : ℝ) := by
    have : ∀ e, (load P e : ℝ) * (if e ∈ A i then a e else 0)
        = if e ∈ A i then a e * load P e else 0 := fun e => by split_ifs <;> ring
    simp_rw [this]; rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h5 : ∑ e, (load P e : ℝ) * a e = ∑ e, a e * (load P e : ℝ) :=
    Finset.sum_congr rfl (fun e _ => by ring)
  linarith

end CongestionPoA.SymSum

open CongestionPoA.SymSum


theorem solution {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : CongestionPoA.AsymSum.IsPureNash G A) (hP : CongestionPoA.AsymSum.IsProfile G P) (i j : Fin N) :
    CongestionPoA.AsymSum.cost G A i ≤ ∑ e ∈ P j, (a e * (CongestionPoA.AsymSum.load A e : ℝ) + b e) + ∑ e ∈ P j \ A i, a e := by
  exact nd_core G a b hlin hsym A P hA hP i j
