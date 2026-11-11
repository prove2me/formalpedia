-- Prove2me | solution 1 for FunctionAlgebras.baker_pixley
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T02:03:23.683627+00:00
-- url     : https://prove2.me/submissions/3f5f88bb-67f5-4331-adc4-e47de84b9313

import Mathlib
import Definitions.Def_FunctionAlgebras_defs

set_option autoImplicit false

universe u

namespace BPAux
open FunctionAlgebras

variable {A : Type u}

/-- Interpolation on any `d` points (possibly repeated): the relation of value tuples of `C n`
at `s 0, ..., s (d-1)` is invariant and contains the projections. -/
lemma interp_d (C : ∀ n : ℕ, Set ((Fin n → A) → A)) (hC : IsClone C) (d n : ℕ)
    (f : (Fin n → A) → A) (hf : ∀ R ∈ Inv C d, Preserves f R)
    (s : Fin d → (Fin n → A)) : ∃ p ∈ C n, ∀ i, p (s i) = f (s i) := by
  classical
  let R : Set (Fin d → A) := {v | ∃ g ∈ C n, v = fun i => g (s i)}
  have hR : R ∈ Inv C d := by
    intro k h hh rows hrows
    choose g hg hgr using hrows
    refine ⟨fun x => h (fun j => g j x), hC.2 k n h g hh hg, ?_⟩
    funext i
    simp [hgr]
  have hproj : ∀ j : Fin n, (fun i => s i j) ∈ R := fun j => ⟨fun x => x j, hC.1 n j, rfl⟩
  obtain ⟨p, hp, hpe⟩ := hf R hR (fun j i => s i j) hproj
  refine ⟨p, hp, fun i => ?_⟩
  have := congrFun hpe i
  exact this.symm

lemma interp_small (C : ∀ n : ℕ, Set ((Fin n → A) → A)) (hC : IsClone C) (d n : ℕ)
    (f : (Fin n → A) → A) (hf : ∀ R ∈ Inv C d, Preserves f R)
    (S : Finset (Fin n → A)) (hS : S.Nonempty) (hcard : S.card ≤ d) :
    ∃ p ∈ C n, ∀ x ∈ S, p x = f x := by
  classical
  obtain ⟨x0, -⟩ := hS
  let s : Fin d → (Fin n → A) := fun i =>
    if h : i.val < S.card then (S.equivFin.symm ⟨i.val, h⟩).val else x0
  obtain ⟨p, hp, hps⟩ := interp_d C hC d n f hf s
  refine ⟨p, hp, fun x hx => ?_⟩
  have hkd : (S.equivFin ⟨x, hx⟩).val < d := lt_of_lt_of_le (S.equivFin ⟨x, hx⟩).isLt hcard
  have hsx : s ⟨(S.equivFin ⟨x, hx⟩).val, hkd⟩ = x := by
    simp [s]
  rw [← hsx]
  exact hps _

lemma interp_all (C : ∀ n : ℕ, Set ((Fin n → A) → A)) (hC : IsClone C) {d : ℕ}
    (hd : 2 ≤ d) (m : (Fin (d + 1) → A) → A) (hm : m ∈ C (d + 1)) (hnu : IsNearUnanimity m)
    (n : ℕ) (f : (Fin n → A) → A) (hf : ∀ R ∈ Inv C d, Preserves f R) :
    ∀ k : ℕ, ∀ S : Finset (Fin n → A), S.card ≤ k → S.Nonempty →
      ∃ p ∈ C n, ∀ x ∈ S, p x = f x := by
  classical
  intro k
  induction k with
  | zero =>
    intro S hS hne
    have := Finset.card_pos.mpr hne
    omega
  | succ k ih =>
    intro S hS hne
    by_cases hsm : S.card ≤ d
    · exact interp_small C hC d n f hf S hne hsm
    have hle : d + 1 ≤ S.card := by omega
    let e : Fin (d + 1) → (Fin n → A) := fun i => (S.equivFin.symm (Fin.castLE hle i)).val
    have he_inj : Function.Injective e := by
      intro i j hij
      have h1 : S.equivFin.symm (Fin.castLE hle i) = S.equivFin.symm (Fin.castLE hle j) :=
        Subtype.ext hij
      exact Fin.castLE_injective hle (S.equivFin.symm.injective h1)
    have heS : ∀ i, e i ∈ S := fun i => (S.equivFin.symm (Fin.castLE hle i)).property
    have hp : ∀ i, ∃ p ∈ C n, ∀ x ∈ S.erase (e i), p x = f x := by
      intro i
      apply ih
      · rw [Finset.card_erase_of_mem (heS i)]; omega
      · rw [← Finset.card_pos, Finset.card_erase_of_mem (heS i)]; omega
    choose p hpC hpS using hp
    refine ⟨fun x => m (fun i => p i x), hC.2 (d + 1) n m p hm hpC, ?_⟩
    intro x hx
    have key : ∀ i0 : Fin (d + 1), (∀ j, j ≠ i0 → x ≠ e j) → m (fun i => p i x) = f x := by
      intro i0 hi0
      have hv : (fun i => p i x) = Function.update (fun _ => f x) i0 (p i0 x) := by
        funext j
        by_cases hj : j = i0
        · subst hj; simp
        · simp only [Function.update, hj, dif_neg, not_false_eq_true]
          exact hpS j x (Finset.mem_erase.mpr ⟨hi0 j hj, hx⟩)
      rw [hv]
      exact hnu i0 (f x) (p i0 x)
    by_cases hex : ∃ i, e i = x
    · obtain ⟨i0, hi0⟩ := hex
      refine key i0 (fun j hj hxe => hj (he_inj ?_))
      rw [← hxe, hi0]
    · exact key 0 (fun j _ hxe => hex ⟨j, hxe.symm⟩)

end BPAux

open FunctionAlgebras in
theorem solution {A : Type u} [Finite A] (C : ∀ n : ℕ, Set ((Fin n → A) → A)) (hC : IsClone C) {d : ℕ}
    (hd : 2 ≤ d) (m : (Fin (d + 1) → A) → A) (hm : m ∈ C (d + 1)) (hnu : IsNearUnanimity m)
    (n : ℕ) (f : (Fin n → A) → A) :
    f ∈ C n ↔ ∀ R ∈ Inv C d, Preserves f R := by
  constructor
  · intro hf R hR
    exact hR n f hf
  · intro hf
    classical
    haveI := Fintype.ofFinite (Fin n → A)
    by_cases hne : (Finset.univ : Finset (Fin n → A)).Nonempty
    · obtain ⟨p, hp, hpe⟩ :=
        BPAux.interp_all C hC hd m hm hnu n f hf _ Finset.univ le_rfl hne
      have hpf : p = f := funext fun x => hpe x (Finset.mem_univ x)
      rwa [hpf] at hp
    · rw [Finset.univ_nonempty_iff, not_nonempty_iff] at hne
      cases n with
      | zero => exact (hne.false (fun i : Fin 0 => i.elim0)).elim
      | succ n =>
        have hf0 : f = fun x => x 0 := funext fun x => (hne.false x).elim
        rw [hf0]
        exact hC.1 _ 0
