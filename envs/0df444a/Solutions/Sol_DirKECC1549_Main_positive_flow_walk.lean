-- Prove2me | solution 1 for DirKECC1549.Main.positive_flow_walk
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T11:06:21.151173+00:00
-- url     : https://prove2.me/submissions/bc44d631-35b2-4976-a1f8-d3add6179f36

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false
open DirKECC1549.Main
open Finset

private theorem support_cut_bound {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (q : ℕ) (F : Finset (Fin m)) (hF : IsUnitFlow D F u v q)
    (S : Finset (Fin n)) (hS : IsCut S u v) :
    (q : ℤ) ≤ ∑ e ∈ F, if (D e).1 ∈ S ∧ (D e).2 ∉ S then (1 : ℤ) else 0 := by
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
  exact hle

private theorem walk_append {n m : ℕ} {D : Fin m → Fin n × Fin n}
    {u v w : Fin n} {p q : List (Fin m)} (hp : IsWalk D u p v) (hq : IsWalk D v q w) :
    IsWalk D u (p ++ q) w := by
  induction hp with
  | nil => simpa using hq
  | cons e p he hw ih => exact IsWalk.cons e (p ++ q) he (ih hq)

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (huv : u ≠ v) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v (q + 1)) :
    ∃ p : List (Fin m), IsWalk D u p v ∧ p.toFinset ⊆ F := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun x ↦
    ∃ p : List (Fin m), IsWalk D u p x ∧ p.toFinset ⊆ F)
  have hS : ∀ x, x ∈ S ↔ ∃ p : List (Fin m), IsWalk D u p x ∧ p.toFinset ⊆ F := by
    intro x; simp [S]
  by_contra hn
  have hu : u ∈ S := (hS u).mpr ⟨[], IsWalk.nil u, by simp⟩
  have hv : v ∉ S := by simpa [hS] using hn
  have hclosed : ∀ e ∈ F, (D e).1 ∈ S → (D e).2 ∈ S := by
    intro e he ht
    obtain ⟨p, hp, hsub⟩ := (hS _).mp ht
    apply (hS _).mpr
    refine ⟨p ++ [e], walk_append hp (IsWalk.cons e [] rfl (IsWalk.nil _)), ?_⟩
    intro a ha
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hsub (List.mem_toFinset.mpr ha)
    · exact he
  have hb := support_cut_bound D u v (q + 1) F hF S ⟨hu, hv⟩
  have hzero : (∑ e ∈ F, if (D e).1 ∈ S ∧ (D e).2 ∉ S then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hh : ¬ ((D e).1 ∈ S ∧ (D e).2 ∉ S) := by
      rintro ⟨ht, hh⟩
      exact hh (hclosed e he ht)
    simp [hh]
  rw [hzero] at hb
  omega
