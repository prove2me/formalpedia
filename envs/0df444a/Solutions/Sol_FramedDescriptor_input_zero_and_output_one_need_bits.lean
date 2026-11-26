-- Prove2me | solution 1 for FramedDescriptor.input_zero_and_output_one_need_bits
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T22:00:53.959902+00:00
-- url     : https://prove2.me/submissions/90afa43a-4d8a-4d40-af5b-4ac121ecc14a

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

theorem solution (w : List Bool)
    (input : ∃ u ∈ rows w, inputSymbol u = some 0)
    (output : ∃ v ∈ rows w, outputSymbol v = some 1) :
    29 ≤ w.length := by
  obtain ⟨u, hu, input⟩ := input
  obtain ⟨v, hv, output⟩ := output
  apply describe_table_bitCost w 26 (by decide)
  have keyCost := input_zero_key_cost u input
  have actCost := output_one_action_cost v output
  by_cases same : u = v
  · have margin := unframe_and_dropFrame_margin u (by
      intro empty
      rw [← same,empty] at actCost
      simp at actCost)
    have tableCost := frame_entry_bitCost _ _ hu
    rw [← same] at actCost
    omega
  · have keyFrameCost := unframe_bitCost u
    have actMargin := dropFrame_margin v (by
      intro empty
      simp [empty] at actCost)
    have tableCost := two_frame_entries_bitCost u v _ same hu hv
    omega

#print axioms solution
