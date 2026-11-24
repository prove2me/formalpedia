-- Prove2me | solution 1 for Formalism.UG.P.satakeInv_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:49.959011+00:00
-- url     : https://prove2.me/submissions/cc590c38-f2bc-46bb-baca-c951e11a7f67

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.UG.P
open Finset
private theorem satakeInv_insert_max_add_card {α : Type} [LinearOrder α] (s S : Finset α) (m : α)
    (hm : ∀ x ∈ S, x < m) (hms : m ∈ s) :
    satakeInv s (insert m S) + S.card = satakeInv s S + (s.filter (fun l => m < l)).card := by
  have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
  unfold satakeInv
  rw [sum_insert hmS]
  have h1 : (s \ insert m S).filter (fun l => m < l) = s.filter (fun l => m < l) := by
    ext x
    simp only [mem_filter, mem_sdiff, mem_insert]
    constructor
    · rintro ⟨⟨hx, -⟩, h⟩
      exact ⟨hx, h⟩
    · rintro ⟨hx, h⟩
      refine ⟨⟨hx, ?_⟩, h⟩
      rintro (rfl | hxS)
      · exact lt_irrefl _ h
      · exact lt_asymm h (hm x hxS)
  have h2 : ∀ a ∈ S, ((s \ S).filter (fun l => a < l)).card
      = ((s \ insert m S).filter (fun l => a < l)).card + 1 := by
    intro a ha
    have e : (s \ S).filter (fun l => a < l)
        = insert m ((s \ insert m S).filter (fun l => a < l)) := by
      ext x
      by_cases hx : x = m
      · simp [hx, hms, hmS, hm a ha]
      · simp [hx]
    rw [e, card_insert_of_notMem (by simp)]
  rw [h1, sum_congr rfl h2, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  ring
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Finset
namespace Formalism.UG.P
theorem _root_.solution {n : ℕ} (S : Finset (Fin n)) :
    2 * (satakeInv univ S : ℤ) =
      ∑ a ∈ S, ((n : ℤ) - 1 - 2 * (a : ℕ)) + (S.card : ℤ) * ((n : ℤ) - S.card) := by
  induction S using Finset.induction_on_max
  next => simp [satakeInv]
  next m S' hm ih =>
    have hmS' : m ∉ S' := fun h => lt_irrefl m (hm m h)
    have L := satakeInv_insert_max_add_card (univ : Finset (Fin n)) S' m hm (mem_univ m)
    have hc : ((univ : Finset (Fin n)).filter (fun l => m < l)).card = n - 1 - (m : ℕ) := by
      rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    rw [hc] at L
    have hlt : (m : ℕ) < n := m.isLt
    have hsub : (((n - 1 - (m : ℕ) : ℕ)) : ℤ) = (n : ℤ) - 1 - (m : ℕ) := by omega
    have L' := congrArg (fun x : ℕ => (x : ℤ)) L
    simp only [Nat.cast_add] at L'
    rw [hsub] at L'
    rw [sum_insert hmS', card_insert_of_notMem hmS']
    push_cast
    linear_combination 2 * L' + ih
end Formalism.UG.P
