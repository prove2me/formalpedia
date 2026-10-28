-- Prove2me | solution 1 for Erdos624.k17_three_colour_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:36:42.032104+00:00
-- url     : https://prove2.me/submissions/8f11db0e-bb94-4be7-84e4-a28060fd7535

import Mathlib
open Finset

namespace E624R13R
open Finset

variable {ι : Type*} [DecidableEq ι]

lemma fin3_key : ∀ a b c c0 : Fin 3, a ≠ c0 → a ≠ c → b ≠ c0 → b ≠ c → c ≠ c0 → a = b := by
  decide

/-- `R(3,3) ≤ 6` inside a set whose edges avoid colour `c0`. -/
lemma two_colour (g : ι → ι → Fin 3) (hg : ∀ x y, g x y = g y x) (c0 : Fin 3) (S : Finset ι)
    (hS : 6 ≤ #S) (havoid : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → g x y ≠ c0) :
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ g x y = g x z ∧ g x y = g y z := by
  obtain ⟨v, hv⟩ : S.Nonempty := card_pos.1 (by omega)
  set S' := S.erase v
  have hS' : 5 ≤ #S' := by rw [card_erase_of_mem hv]; omega
  have hmaps : ∀ x ∈ S', g v x ∈ (univ.erase c0 : Finset (Fin 3)) := by
    intro x hx; rw [mem_erase] at hx ⊢
    exact ⟨havoid v hv x hx.2 (Ne.symm hx.1), mem_univ _⟩
  obtain ⟨c, hc, hcard⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
    (n := 2) (by rw [card_erase_of_mem (mem_univ _)]; simp; omega)
  set N := S'.filter (fun x => g v x = c)
  have hNS : N ⊆ S := (filter_subset _ _).trans (erase_subset _ _)
  have hvN : v ∉ N := fun h => by simp [N, S'] at h
  by_cases hin : ∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ g x y = c
  · obtain ⟨x, hx, y, hy, hxy, hc'⟩ := hin
    have hgx : g v x = c := (mem_filter.1 hx).2
    have hgy : g v y = c := (mem_filter.1 hy).2
    refine ⟨v, hv, x, hNS hx, y, hNS hy, fun h => hvN (h ▸ hx), fun h => hvN (h ▸ hy), hxy,
      by rw [hgx, hgy], by rw [hgx, hc']⟩
  · push Not at hin
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.1 hcard
    have hc0 : c ≠ c0 := (mem_erase.1 hc).1
    have key : ∀ a b : Fin 3, a ≠ c0 → a ≠ c → b ≠ c0 → b ≠ c → a = b :=
      fun a b h1 h2 h3 h4 => fin3_key a b c c0 h1 h2 h3 h4 hc0
    refine ⟨x, hNS hx, y, hNS hy, z, hNS hz, hxy, hxz, hyz, ?_, ?_⟩
    · exact key _ _ (havoid x (hNS hx) y (hNS hy) hxy) (hin x hx y hy hxy)
        (havoid x (hNS hx) z (hNS hz) hxz) (hin x hx z hz hxz)
    · exact key _ _ (havoid x (hNS hx) y (hNS hy) hxy) (hin x hx y hy hxy)
        (havoid y (hNS hy) z (hNS hz) hyz) (hin y hy z hz hyz)

lemma three_colour (g : ι → ι → Fin 3) (hg : ∀ x y, g x y = g y x) (S : Finset ι)
    (hS : 17 ≤ #S) :
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ g x y = g x z ∧ g x y = g y z := by
  obtain ⟨v, hv⟩ : S.Nonempty := card_pos.1 (by omega)
  set S' := S.erase v
  have hS' : 16 ≤ #S' := by rw [card_erase_of_mem hv]; omega
  have hmaps : ∀ x ∈ S', g v x ∈ (univ : Finset (Fin 3)) := fun _ _ => mem_univ _
  obtain ⟨c, -, hcard⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
    (n := 5) (by simp; omega)
  set N := S'.filter (fun x => g v x = c)
  have hNS : N ⊆ S := (filter_subset _ _).trans (erase_subset _ _)
  have hvN : v ∉ N := fun h => by simp [N, S'] at h
  by_cases hin : ∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ g x y = c
  · obtain ⟨x, hx, y, hy, hxy, hc'⟩ := hin
    have hgx : g v x = c := (mem_filter.1 hx).2
    have hgy : g v y = c := (mem_filter.1 hy).2
    refine ⟨v, hv, x, hNS hx, y, hNS hy, fun h => hvN (h ▸ hx), fun h => hvN (h ▸ hy), hxy,
      by rw [hgx, hgy], by rw [hgx, hc']⟩
  · push Not at hin
    obtain ⟨x, hx, y, hy, z, hz, h1, h2, h3, h4, h5⟩ :=
      two_colour g hg c N (by omega) (fun x hx y hy hxy => hin x hx y hy hxy)
    exact ⟨x, hNS hx, y, hNS hy, z, hNS hz, h1, h2, h3, h4, h5⟩

end E624R13R

namespace Erdos624

theorem k17_three_colour_ramsey (g : Fin 17 → Fin 17 → Fin 3) (hg : ∀ x y, g x y = g y x) :
    ∃ x y z : Fin 17, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ g x y = g x z ∧ g x y = g y z := by
  obtain ⟨x, -, y, -, z, -, h⟩ := E624R13R.three_colour g hg Finset.univ (by simp)
  exact ⟨x, y, z, h⟩

end Erdos624

open Finset

theorem solution (g : Fin 17 → Fin 17 → Fin 3) (hg : ∀ x y, g x y = g y x) :
    ∃ x y z : Fin 17, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ g x y = g x z ∧ g x y = g y z :=
  Erdos624.k17_three_colour_ramsey g hg
