-- Prove2me | solution 1 for FramedDescriptor.two_input_symbols_and_output_one_need_bits
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T22:02:27.120967+00:00
-- url     : https://prove2.me/submissions/b53273ed-728b-4b62-9ecc-2fa93b600710

import Definitions.Def_FramedDescriptorBitWidth

open Turing.MultiTapeTM FramedDescriptor

private theorem unframe_bitCost (w : List Bool) : 2 * (unframe w).length ≤ w.length := by
  match w with
  | [] => simp [unframe]
  | false :: _ => simp [unframe]
  | [true] => simp [unframe]
  | true :: b :: rest =>
    have smaller := unframe_bitCost rest
    simp only [unframe,List.length_cons]
    omega

private theorem frame_entry_bitCost (u w : List Bool) (present : u ∈ frames w) :
    2 * u.length ≤ w.length := by
  by_cases empty : w = []
  · simp [empty] at present
  · rw [frames_of_ne_nil empty] at present
    rcases List.mem_cons.mp present with rfl | inTail
    · exact unframe_bitCost w
    · exact (frame_entry_bitCost u (dropFrame w) inTail).trans
        (length_dropFrame_lt empty).le
termination_by w.length
decreasing_by exact length_dropFrame_lt empty

private theorem dropFrame_margin (w : List Bool) (nonempty : dropFrame w ≠ []) :
    (dropFrame w).length + 1 ≤ w.length := by
  apply length_dropFrame_lt
  intro empty
  exact nonempty (by simp [empty,dropFrame])

private theorem two_dropFrame_margin (w : List Bool) (nonempty : dropFrame (dropFrame w) ≠ []) :
    (dropFrame (dropFrame w)).length + 2 ≤ w.length := by
  have first : dropFrame w ≠ [] := by
    intro empty
    exact nonempty (by simp [empty,dropFrame])
  have a := dropFrame_margin (dropFrame w) nonempty
  have b := dropFrame_margin w first
  omega

private theorem symbol_one_needs_two (w : List Bool)
    (output : (Decoder.unary.option).decode w = some 1) : w.length = 2 := by
  cases w with
  | nil => simp [Decoder.option] at output
  | cons bit rest =>
    have length : rest.length = 1 := by simpa [Decoder.option,Decoder.unary] using output
    simp [length]

private theorem nonempty_afterMarker_margin (w : List Bool) (nonempty : afterMarker w ≠ []) :
    (afterMarker w).length + 1 ≤ w.length := by
  induction w with
  | nil => exact (nonempty rfl).elim
  | cons bit rest ih =>
    cases bit with
    | false => exact (ih nonempty).trans (Nat.le_succ _)
    | true => simp [afterMarker]

private theorem output_one_action_cost (u : List Bool)
    (output : (Decoder.unary.option).decode
      (unframe (dropFrame (dropFrame (dropFrame u)))) = some 1) :
    6 ≤ (dropFrame u).length := by
  let actBytes := dropFrame u
  let outputStart := dropFrame (dropFrame actBytes)
  have needOutput : 4 ≤ outputStart.length := by
    have needed := symbol_one_needs_two _ output
    have consumed := unframe_bitCost outputStart
    change (unframe outputStart).length = 2 at needed
    omega
  have margin := two_dropFrame_margin actBytes (by
    intro empty
    change outputStart = [] at empty
    simp [empty] at needOutput)
  change outputStart.length + 2 ≤ actBytes.length at margin
  change 6 ≤ actBytes.length
  omega

private theorem describe_table_bitCost (w : List Bool) (k : ℕ) (positive : 0 < k)
    (table : k ≤ (dropFrame (dropFrame (afterMarker w))).length) :
    k + 3 ≤ w.length := by
  have nonemptyTable : dropFrame (dropFrame (afterMarker w)) ≠ [] := by
    intro empty
    simp only [empty,List.length_nil] at table
    omega
  have descriptor := two_dropFrame_margin (afterMarker w) nonemptyTable
  have nonemptyAfter : afterMarker w ≠ [] := by
    intro empty
    exact nonemptyTable (by simp [empty,dropFrame])
  have skipMarker := nonempty_afterMarker_margin w nonemptyAfter
  omega

private theorem unframe_and_dropFrame_cost (w : List Bool) :
    2 * (unframe w).length + (dropFrame w).length ≤ w.length := by
  match w with
  | [] => simp [unframe, dropFrame]
  | false :: _ => simp [unframe, dropFrame]
  | [true] => simp [unframe, dropFrame]
  | true :: b :: rest =>
    have smaller := unframe_and_dropFrame_cost rest
    simp only [unframe,dropFrame,List.length_cons]
    omega

private theorem unframe_and_dropFrame_margin (w : List Bool) (nonempty : dropFrame w ≠ []) :
    2 * (unframe w).length + (dropFrame w).length + 1 ≤ w.length := by
  match w with
  | [] => exact (nonempty rfl).elim
  | false :: _ => simp [unframe, dropFrame]
  | [true] => exact (nonempty rfl).elim
  | true :: b :: rest =>
    have smaller := unframe_and_dropFrame_margin rest nonempty
    simp only [unframe,dropFrame,List.length_cons]
    omega

private theorem two_frame_entries_bitCost (u v w : List Bool) (diff : u ≠ v)
    (hu : u ∈ frames w) (hv : v ∈ frames w) :
    2*u.length + 2*v.length ≤ w.length := by
  by_cases empty : w = []
  · simp [empty] at hu
  rw [frames_of_ne_nil empty,List.mem_cons] at hu hv
  rcases hu with h | h <;> rcases hv with h' | h'
  · exact (diff (h.trans h'.symm)).elim
  · have vcost := frame_entry_bitCost v (dropFrame w) h'
    have total := unframe_and_dropFrame_cost w
    rw [h]
    omega
  · have ucost := frame_entry_bitCost u (dropFrame w) h
    have total := unframe_and_dropFrame_cost w
    rw [h']
    omega
  · exact (two_frame_entries_bitCost u v (dropFrame w) diff h h').trans
      (length_dropFrame_lt empty).le
termination_by w.length
decreasing_by exact length_dropFrame_lt empty

private theorem input_zero_key_cost (u : List Bool)
    (input : (Decoder.unary.option).decode (unframe (dropFrame (unframe u))) = some 0) :
    3 ≤ (unframe u).length := by
  have ne : unframe (dropFrame (unframe u)) ≠ [] := by
    intro empty
    simp [empty,Decoder.option] at input
  have cost := unframe_bitCost (dropFrame (unframe u))
  have pos := List.length_pos_iff.mpr ne
  have margin := dropFrame_margin (unframe u) (by
    intro empty
    exact ne (by simp [empty,unframe]))
  omega

private theorem frames_total_bitCost (w : List Bool) :
    2 * ((frames w).map List.length).sum ≤ w.length := by
  by_cases blank : w = []
  · simp [blank]
  · rw [frames_of_ne_nil blank,List.map_cons,List.sum_cons]
    have cost := unframe_and_dropFrame_cost w
    have tail := frames_total_bitCost (dropFrame w)
    omega
termination_by w.length
decreasing_by exact length_dropFrame_lt blank

private theorem distinct_frame_entries_bitCost (rows : List (List Bool)) (w : List Bool) (distinct : rows.Nodup)
    (included : rows ⊆ frames w) : 2 * (rows.map List.length).sum ≤ w.length := by
  obtain ⟨sub,perm,contained⟩ := distinct.subperm included
  have summed := (perm.map List.length).sum_eq
  have bounded := (contained.map List.length).sum_le_sum (fun _ _ => Nat.zero_le _)
  have cost := frames_total_bitCost w
  omega

private theorem input_one_key_cost (u : List Bool)
    (input : (Decoder.unary.option).decode (unframe (dropFrame (unframe u))) = some 1) :
    5 ≤ (unframe u).length := by
  have need := symbol_one_needs_two _ input
  have cost := unframe_bitCost (dropFrame (unframe u))
  have margin := dropFrame_margin (unframe u) (by
    intro empty
    simp [empty,unframe] at need)
  omega

theorem solution (w : List Bool)
    (inputZero : ∃ u ∈ rows w, inputSymbol u = some 0)
    (inputOne : ∃ v ∈ rows w, inputSymbol v = some 1)
    (output : ∃ z ∈ rows w, outputSymbol z = some 1) :
    49 ≤ w.length := by
  obtain ⟨u, hu, readsZero⟩ := inputZero
  obtain ⟨v, hv, readsOne⟩ := inputOne
  obtain ⟨z, hz, emitsOne⟩ := output
  change (Decoder.unary.option).decode (unframe (dropFrame (unframe u))) = some 0 at readsZero
  change (Decoder.unary.option).decode (unframe (dropFrame (unframe v))) = some 1 at readsOne
  have separateKeys : u ≠ v := by
    intro eq
    rw [eq,readsOne] at readsZero
    cases readsZero
  have zeroKey := input_zero_key_cost u readsZero
  have oneKey := input_one_key_cost v readsOne
  have emission := output_one_action_cost z emitsOne
  have nonemptyAction : dropFrame z ≠ [] := by
    intro eq
    simp [eq] at emission
  have bareZero := unframe_bitCost u
  have bareOne := unframe_bitCost v
  apply describe_table_bitCost w 46 (by decide)
  by_cases sharedWithZero : z = u
  · rw [sharedWithZero] at emission nonemptyAction
    have shared := unframe_and_dropFrame_margin u nonemptyAction
    have table := two_frame_entries_bitCost _ _ _ separateKeys hu hv
    omega
  · by_cases sharedWithOne : z = v
    · rw [sharedWithOne] at emission nonemptyAction
      have shared := unframe_and_dropFrame_margin v nonemptyAction
      have table := two_frame_entries_bitCost _ _ _ separateKeys hu hv
      omega
    · have bareEmit := dropFrame_margin z nonemptyAction
      have table := distinct_frame_entries_bitCost [u,v,z] _
        (by simp [separateKeys,Ne.symm sharedWithZero,Ne.symm sharedWithOne]) (by
          intro row inRows
          simp only [List.mem_cons,List.not_mem_nil,or_false] at inRows
          rcases inRows with rfl | rfl | rfl
          · exact hu
          · exact hv
          · exact hz)
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at table
      omega

#print axioms solution
