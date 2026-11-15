-- Prove2me | solution 1 for DirKECC1549.Main.reverse_scan_trace_invariants
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-14T15:51:15.948862+00:00
-- url     : https://prove2.me/submissions/0aad82c9-efdd-4734-b17d-4630b990ad2a

import Definitions.Def_DirKECC1549_Main_ReverseScanTrace
set_option autoImplicit false
open DirKECC1549.Main

theorem solution {n m : ℕ} (G : Fin m → Fin n × Fin n) (r : Fin n)
    {par : Fin n → Fin n} {order : List (Fin n)} {scanned : Finset (Fin m)}
    (ht : ReverseScanTrace G r par order scanned) :
    par r = r ∧ order.Nodup ∧ r ∈ order ∧
      (∀ v ∈ order, v ≠ r → (∃ e, G e = (v, par v)) ∧ par v ∈ order ∧
        order.idxOf (par v) < order.idxOf v) ∧
      ∀ e ∈ scanned, (G e).1 ∈ order := by
  induction ht with
  | initial => simp
  | @seen par order scanned ht e hhead htail ih =>
    obtain ⟨hroot, hnodup, hr, hparent, hscanned⟩ := ih
    refine ⟨hroot, hnodup, hr, hparent, ?_⟩
    intro e' he'
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact htail
    · exact hscanned e' he'
  | @fresh par order scanned ht e hhead htail ih =>
    obtain ⟨hroot, hnodup, hr, hparent, hscanned⟩ := ih
    have hrne : r ≠ (G e).1 := by
      intro h
      exact htail (h ▸ hr)
    refine ⟨?_, ?_, List.mem_append_left _ hr, ?_, ?_⟩
    · simpa only [Function.update_of_ne hrne] using hroot
    · simpa using hnodup.concat htail
    · intro v hv hvr
      rcases List.mem_append.mp hv with hv | hv
      · have hvne : v ≠ (G e).1 := by
          intro h
          exact htail (h ▸ hv)
        rw [Function.update_of_ne hvne]
        obtain ⟨hedge, hparmem, hlt⟩ := hparent v hv hvr
        refine ⟨hedge, List.mem_append_left _ hparmem, ?_⟩
        simpa only [List.idxOf_append_of_mem hparmem, List.idxOf_append_of_mem hv] using hlt
      · have hv' : v = (G e).1 := List.mem_singleton.mp hv
        subst v
        rw [Function.update_self]
        refine ⟨⟨e, rfl⟩, List.mem_append_left _ hhead, ?_⟩
        rw [List.idxOf_append_of_mem hhead, List.idxOf_append_of_notMem htail]
        simpa using List.idxOf_lt_length_of_mem hhead
    · intro e' he'
      rcases Finset.mem_insert.mp he' with rfl | he'
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ (hscanned e' he')
