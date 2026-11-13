-- Prove2me | solution 1 for DirKECC1549.Main.unit_flow_toggle_residual_trail
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T11:22:33.99451+00:00
-- url     : https://prove2.me/submissions/627731d4-97c5-435f-8a63-5deeae7610bd

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false
open DirKECC1549.Main
open Finset

private theorem trail_balance {n m : ℕ} (D : Fin m → Fin n × Fin n)
    {u v : Fin n} {p : List (Fin m)} (hw : IsWalk D u p v) (hn : p.Nodup) :
    IsUnitFlow D p.toFinset u v 1 := by
  classical
  induction hw with
  | nil => intro x; simp
  | @cons u v e p ht hw ih =>
    have hnot : e ∉ p := (List.nodup_cons.mp hn).1
    have hnodup : p.Nodup := (List.nodup_cons.mp hn).2
    have hrec := ih hnodup
    intro x
    have hr := hrec x
    have hnF : e ∉ p.toFinset := by simpa using hnot
    by_cases htail : (D e).1 = x <;> by_cases hhead : (D e).2 = x
    all_goals simp [List.toFinset_cons, Finset.filter_insert, htail, hhead,
      hnF, Finset.card_insert_of_notMem] at hr ⊢
    all_goals subst_vars <;> simp_all <;> omega

private theorem balance_sum {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (F : Finset (Fin m)) (x : Fin n) :
    ((F.filter (fun e ↦ (D e).1 = x)).card : ℤ) -
      ((F.filter (fun e ↦ (D e).2 = x)).card : ℤ) =
    ∑ e ∈ Finset.univ, if e ∈ F then
      ((if (D e).1 = x then (1 : ℤ) else 0) - (if (D e).2 = x then 1 else 0)) else 0 := by
  classical
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  symm
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v q) (p : List (Fin m))
    (hp : IsTrail (flipEdges D F) u p v) :
    IsUnitFlow D ((F \ p.toFinset) ∪ (p.toFinset \ F)) u v (q + 1) := by
  classical
  have htrail := trail_balance (flipEdges D F) hp.1 hp.2
  intro x
  have h1 := hF x
  have h2 := htrail x
  rw [balance_sum] at h1 h2 ⊢
  have hsum :
      (∑ e ∈ Finset.univ, if e ∈ (F \ p.toFinset) ∪ (p.toFinset \ F) then
        ((if (D e).1 = x then (1 : ℤ) else 0) - (if (D e).2 = x then 1 else 0)) else 0) =
      (∑ e ∈ Finset.univ, if e ∈ F then
        ((if (D e).1 = x then (1 : ℤ) else 0) - (if (D e).2 = x then 1 else 0)) else 0) +
      (∑ e ∈ Finset.univ, if e ∈ p.toFinset then
        ((if ((flipEdges D F) e).1 = x then (1 : ℤ) else 0) -
          (if ((flipEdges D F) e).2 = x then 1 else 0)) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hf : e ∈ F <;> by_cases hp : e ∈ p.toFinset <;>
      by_cases ht : (D e).1 = x <;> by_cases hh : (D e).2 = x <;>
      simp [hf, hp, ht, hh, flipEdges]
  rw [hsum, h1, h2]
  push_cast
  split_ifs <;> omega
