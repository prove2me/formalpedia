-- Prove2me | solution 1 for ClassicalSchur.color_eq_of_card_filter_eq
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:31:03.364571+00:00
-- url     : https://prove2.me/submissions/8c315579-0a00-4ecb-b773-692f56b0308b

-- Generated from lean/ClassicalSchur/Midpoint.lean
--   imports : 0 platform node(s), 0 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : color_eq_of_card_filter_eq -> solution, hoisted out of the namespace
import Mathlib

open Finset

theorem solution {α γ : Type*} [DecidableEq α] [DecidableEq γ]
    (col : α → α → γ) {W : Finset α} {e : α} (he : e ∉ W) (J : α → α)
    (hJ : ∀ x ∈ W, J x ∈ W) (hJJ : ∀ x ∈ W, J (J x) = x)
    (hcol : ∀ x ∈ W, ∀ y ∈ W, col (J x) (J y) = col x y) {v : α} (hv : v ∈ W)
    (hdeg : ∀ i, (((insert e W).erase v).filter fun w => col v w = i).card =
      (((insert e W).erase (J v)).filter fun w => col (J v) w = i).card) :
    col v e = col (J v) e := by
  have hJv := hJ v hv
  -- the neighbours in `W` correspond by `J`
  have hW : ∀ i, ((W.erase v).filter fun w => col v w = i).card =
      ((W.erase (J v)).filter fun w => col (J v) w = i).card := by
    intro i
    apply card_nbij' J J
    · intro w hw
      obtain ⟨hw1, hw2⟩ := mem_filter.mp hw
      obtain ⟨hwv, hwW⟩ := mem_erase.mp hw1
      refine mem_filter.mpr ⟨mem_erase.mpr ⟨fun h => hwv ?_, hJ w hwW⟩, ?_⟩
      · rw [← hJJ w hwW, h, hJJ v hv]
      · rw [hcol v hv w hwW]
        exact hw2
    · intro w hw
      obtain ⟨hw1, hw2⟩ := mem_filter.mp hw
      obtain ⟨hwv, hwW⟩ := mem_erase.mp hw1
      refine mem_filter.mpr ⟨mem_erase.mpr ⟨fun h => hwv ?_, hJ w hwW⟩, ?_⟩
      · rw [← h, hJJ w hwW]
      · rw [← hJJ v hv, hcol (J v) hJv w hwW]
        exact hw2
    · intro w hw
      exact hJJ w (mem_erase.mp (mem_filter.mp hw).1).2
    · intro w hw
      exact hJJ w (mem_erase.mp (mem_filter.mp hw).1).2
  have hev : e ≠ v := fun h => he (h ▸ hv)
  have heJv : e ≠ J v := fun h => he (h ▸ hJv)
  have h := hdeg (col v e)
  rw [erase_insert_of_ne hev, erase_insert_of_ne heJv, filter_insert, filter_insert,
    if_pos rfl, card_insert_of_notMem (fun h => he (mem_of_mem_erase (mem_filter.mp h).1))] at h
  by_contra hne
  rw [if_neg (Ne.symm hne), hW] at h
  omega
