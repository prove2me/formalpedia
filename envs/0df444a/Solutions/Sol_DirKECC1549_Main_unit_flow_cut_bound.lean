-- Prove2me | solution 1 for DirKECC1549.Main.unit_flow_cut_bound
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:41:10.064581+00:00
-- url     : https://prove2.me/submissions/35908347-7062-4f3b-a58a-bcefafb5835a

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false
open DirKECC1549.Main
open Finset

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (q : ℕ) (F : Finset (Fin m)) (hF : IsUnitFlow D F u v q)
    (S : Finset (Fin n)) (hS : IsCut S u v) : q ≤ outCount D S := by
  classical
  have hu : u ∈ S := hS.1
  have hv : v ∉ S := hS.2
  have hs' : (∑ x ∈ S, (((F.filter (fun e ↦ (D e).1 = x)).card : ℤ) -
      (F.filter (fun e ↦ (D e).2 = x)).card)) = q := by
    calc
      _ = ∑ x ∈ S, ((if x = u then (q : ℤ) else 0) -
          (if x = v then (q : ℤ) else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hF x
      _ = q := by simp [Finset.sum_sub_distrib, hu, hv]
  have ht : (∑ x ∈ S, ((F.filter (fun e ↦ (D e).1 = x)).card : ℤ)) =
      ∑ e ∈ F, if (D e).1 ∈ S then (1 : ℤ) else 0 := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp
  have hh : (∑ x ∈ S, ((F.filter (fun e ↦ (D e).2 = x)).card : ℤ)) =
      ∑ e ∈ F, if (D e).2 ∈ S then (1 : ℤ) else 0 := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp
  rw [Finset.sum_sub_distrib, ht, hh, ← Finset.sum_sub_distrib] at hs'
  have hle : (q : ℤ) ≤ ∑ e ∈ F, if (D e).1 ∈ S ∧ (D e).2 ∉ S then (1 : ℤ) else 0 := by
    rw [← hs']
    apply Finset.sum_le_sum
    intro e he
    by_cases ht : (D e).1 ∈ S <;> by_cases hh : (D e).2 ∈ S <;> simp [ht, hh]
  have hcard : (∑ e ∈ F, if (D e).1 ∈ S ∧ (D e).2 ∉ S then (1 : ℤ) else 0) ≤
      (outCount D S : ℤ) := by
    have hsubl : F.filter (fun e ↦ (D e).1 ∈ S ∧ (D e).2 ∉ S) ⊆ outEdges D S := by
      intro e he
      simp only [Finset.mem_filter] at he
      simp [outEdges, he.2]
    have hh := Finset.card_le_card hsubl
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hh ⊢
    exact_mod_cast hh
  exact_mod_cast hle.trans hcard
