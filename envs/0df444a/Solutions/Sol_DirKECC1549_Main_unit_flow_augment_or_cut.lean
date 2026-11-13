-- Prove2me | solution 1 for DirKECC1549.Main.unit_flow_augment_or_cut
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T11:13:36.616834+00:00
-- url     : https://prove2.me/submissions/85e9056f-2c29-46de-8df0-7379ed07698f

import Theorems.Thm_DirKECC1549_Main_unit_flow_residual_augment
set_option autoImplicit false
open DirKECC1549.Main
open Finset

private theorem append_walk {n m : ℕ} {D : Fin m → Fin n × Fin n}
    {x y z : Fin n} {p q : List (Fin m)} (hp : IsWalk D x p y) (hq : IsWalk D y q z) :
    IsWalk D x (p ++ q) z := by
  induction hp with
  | nil => simpa using hq
  | cons e p ht hw ih => exact IsWalk.cons e (p ++ q) ht (ih hq)

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (huv : u ≠ v) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v q) :
    (∃ F' : Finset (Fin m), IsUnitFlow D F' u v (q + 1)) ∨
      ∃ S : Finset (Fin n), IsCut S u v ∧ outCount D S = q := by
  classical
  by_cases hr : Reach (flipEdges D F) u v
  · exact Or.inl (unit_flow_residual_augment D u v huv q F hF hr)
  · right
    let S : Finset (Fin n) := Finset.univ.filter (fun x ↦ Reach (flipEdges D F) u x)
    have hS : ∀ x, x ∈ S ↔ Reach (flipEdges D F) u x := by intro x; simp [S]
    have hu : u ∈ S := (hS u).mpr ⟨[], IsWalk.nil u⟩
    have hv : v ∉ S := by simpa [hS] using hr
    have hclosed : ∀ e, ((flipEdges D F) e).1 ∈ S → ((flipEdges D F) e).2 ∈ S := by
      intro e he
      obtain ⟨p, hp⟩ := (hS _).mp he
      apply (hS _).mpr
      exact ⟨p ++ [e], append_walk hp (IsWalk.cons e [] rfl (IsWalk.nil _))⟩
    have hout : ∀ e, (D e).1 ∈ S → (D e).2 ∉ S → e ∈ F := by
      intro e ht hh
      by_contra he
      have := hclosed e (by simpa [flipEdges, he] using ht)
      exact hh (by simpa [flipEdges, he] using this)
    have hin : ∀ e ∈ F, (D e).2 ∈ S → (D e).1 ∈ S := by
      intro e he hh
      have := hclosed e (by simpa [flipEdges, he] using hh)
      simpa [flipEdges, he] using this
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
    have hsum : (∑ e ∈ F, ((if (D e).1 ∈ S then (1 : ℤ) else 0) -
        (if (D e).2 ∈ S then 1 else 0))) =
        ∑ e ∈ Finset.univ, if (D e).1 ∈ S ∧ (D e).2 ∉ S then (1 : ℤ) else 0 := by
      calc
        _ = ∑ e ∈ F, if (D e).1 ∈ S ∧ (D e).2 ∉ S then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          by_cases ha : (D e).1 ∈ S <;> by_cases hb : (D e).2 ∈ S
          all_goals simp_all
        _ = ∑ e ∈ Finset.univ, if (D e).1 ∈ S ∧ (D e).2 ∉ S then (1 : ℤ) else 0 := by
          apply Finset.sum_subset (Finset.subset_univ F)
          intro e he hnot
          have hn : ¬ ((D e).1 ∈ S ∧ (D e).2 ∉ S) := by
            rintro ⟨ha, hb⟩
            exact hnot (hout e ha hb)
          simp [hn]
    refine ⟨S, ⟨hu, hv⟩, ?_⟩
    have hcard : (∑ e ∈ Finset.univ, if (D e).1 ∈ S ∧ (D e).2 ∉ S then (1 : ℤ) else 0) =
        (outCount D S : ℤ) := by
      change _ = ((Finset.univ.filter (fun e ↦ (D e).1 ∈ S ∧ (D e).2 ∉ S)).card : ℤ)
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [hsum, hcard] at hs'
    exact_mod_cast hs'
