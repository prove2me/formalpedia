-- Prove2me | solution 1 for EditGV897.Main.expectation_row_programs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:55:57.664146+00:00
-- url     : https://prove2.me/submissions/e792668c-2d66-45ef-b6c5-53c19bed7444

import Definitions.Def_EditGV897_Main_Codec
import Theorems.Thm_EditGV897_Main_witness_count_correct
import Definitions.Def_EditGV897_Main_Machine
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
namespace EditGV897.Main

 theorem bit_zero_or_one (a : Bit) : a = 0 ∨ a = 1 := by
  fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl


@[simp] theorem wordList_length {n : ℕ} (x : Word n) : (wordList x).length = n := by
  simp [wordList, DeletionHash.MixedEdit.letters]

@[simp] theorem listWord_wordList {n : ℕ} (x : Word n) : listWord n (wordList x) = x := by
  funext i
  simp [listWord, wordList, DeletionHash.MixedEdit.letters]

theorem wordList_listWord {n : ℕ} (p : List Bit) (hp : p.length = n) :
    wordList (listWord n p) = p := by
  apply List.ext_getElem
  · simp [hp]
  · intro i hi hj
    simp only [wordList, DeletionHash.MixedEdit.letters, List.getElem_ofFn, listWord]
    simp [List.getElem?_eq_getElem, hj]

theorem witnessCount_correct {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) :
    witnessCount F G E = witnessSum F G (affineSet E) := witness_count_correct n F G E
end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main

def Motion.offset : Motion → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

def Tape.readAt (s : Tape) : ℤ → Option Bool
  | .ofNat 0 => s.head
  | .ofNat (k + 1) => s.right[k]?.getD none
  | .negSucc k => s.left[k]?.getD none

 theorem Tape.readAt_zero (s : Tape) : s.readAt 0 = s.head := rfl

 theorem Tape.readAt_right (s : Tape) (a : Option Bool) (z : ℤ) :
    (s.writeMove a .right).readAt z = if z = -1 then a else s.readAt (z + 1) := by
  cases z with
  | ofNat k =>
    have hn : Int.ofNat k ≠ -1 := by simp only [Int.ofNat_eq_natCast]; omega
    rw [if_neg hn]
    cases k with
    | zero =>
      have he : Int.ofNat 0 + 1 = Int.ofNat 1 := by decide
      rw [he]
      change s.right.headD none = s.right[0]?.getD none
      cases hr : s.right <;> simp [hr, List.headD]
    | succ k =>
      have he : Int.ofNat (k + 1) + 1 = Int.ofNat (k + 2) := by simp only [Int.ofNat_eq_natCast]; omega
      rw [he]
      simp [Tape.writeMove, Tape.readAt, List.getElem?_drop]
  | negSucc k =>
    cases k with
    | zero => rfl
    | succ k =>
      have hn : Int.negSucc (k + 1) ≠ -1 := by omega
      have he : Int.negSucc (k + 1) + 1 = Int.negSucc k := by omega
      rw [if_neg hn, he]
      rfl

 theorem Tape.readAt_left (s : Tape) (a : Option Bool) (z : ℤ) :
    (s.writeMove a .left).readAt z = if z = 1 then a else s.readAt (z - 1) := by
  cases z with
  | ofNat k =>
    cases k with
    | zero =>
      have hn : Int.ofNat 0 ≠ (1 : ℤ) := by decide
      have he : Int.ofNat 0 - 1 = Int.negSucc 0 := by decide
      rw [if_neg hn, he]
      change s.left.headD none = s.left[0]?.getD none
      cases hl : s.left <;> simp [hl, List.headD]
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        have hn : Int.ofNat (k + 1 + 1) ≠ 1 := by simp only [Int.ofNat_eq_natCast]; omega
        have he : Int.ofNat (k + 1 + 1) - 1 = Int.ofNat (k + 1) := by simp only [Int.ofNat_eq_natCast]; omega
        rw [if_neg hn, he]
        rfl
  | negSucc k =>
    have hn : Int.negSucc k ≠ 1 := by omega
    have he : Int.negSucc k - 1 = Int.negSucc (k + 1) := by omega
    rw [if_neg hn, he]
    simp [Tape.writeMove, Tape.readAt, List.getElem?_drop]

 theorem Tape.readAt_writeMove (s : Tape) (a : Option Bool) (m : Motion) (z : ℤ) :
    (s.writeMove a m).readAt z =
      if z + m.offset = 0 then a else s.readAt (z + m.offset) := by
  cases m with
  | right =>
    rw [Tape.readAt_right]
    simp only [Motion.offset]
    have he : z = -1 ↔ z + 1 = 0 := by omega
    simp only [he]
  | left =>
    rw [Tape.readAt_left]
    simp only [Motion.offset]
    have he : z = 1 ↔ z + -1 = 0 := by omega
    simp only [he, sub_eq_add_neg]
  | stay =>
    simp only [Motion.offset, add_zero]
    cases z with
    | ofNat k => cases k <;> rfl
    | negSucc k => rfl

 theorem Tape.blank_readAt (z : ℤ) : (⟨[], none, []⟩ : Tape).readAt z = none := by
  cases z with
  | ofNat k => cases k <;> rfl
  | negSucc k => rfl

def Tape.Represents (s : Tape) (w : ℤ → Option Bool) (p : ℤ) : Prop :=
  ∀ z : ℤ, s.readAt z = w (p + z)

 theorem Tape.represents_blank (p : ℤ) :
    (⟨[], none, []⟩ : Tape).Represents (fun _ => none) p := by
  intro z
  exact Tape.blank_readAt z

 theorem Tape.represents_writeMove (s : Tape) (w : ℤ → Option Bool) (p : ℤ)
    (hs : s.Represents w p) (a : Option Bool) (m : Motion) :
    (s.writeMove a m).Represents (Function.update w p a) (p + m.offset) := by
  intro z
  rw [Tape.readAt_writeMove, hs]
  simp only [Function.update_apply]
  by_cases hz : z + m.offset = 0
  · have he : p + m.offset + z = p := by omega
    simp [hz, he]
  · have he : p + m.offset + z ≠ p := by omega
    simp only [if_neg hz, if_neg he]
    congr 1
    ring

 theorem Tape.represents_move (s : Tape) (w : ℤ → Option Bool) (p : ℤ)
    (hs : s.Represents w p) (m : Motion) :
    (s.writeMove s.head m).Represents w (p + m.offset) := by
  have hh : s.head = w p := by simpa only [Tape.readAt_zero, add_zero] using hs 0
  have hu : Function.update w p s.head = w := by rw [hh]; exact Function.update_eq_self _ _
  simpa only [hu] using s.represents_writeMove w p hs s.head m

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main

 def Motion.ofSign : SignType → Motion
  | .neg => .left
  | .zero => .stay
  | .pos => .right

 theorem Motion.offset_ofSign (s : SignType) : (Motion.ofSign s).offset = (s.cast : ℤ) := by
  cases s <;> rfl

 def inputMotion (s : SignType) (input marker : Option Bool) : Motion :=
  match s with
  | .neg => if marker = some true then .stay else .left
  | .zero => .stay
  | .pos => if input = none ∧ marker ≠ some true then .stay else .right

 noncomputable def stateCode {State : Type} [Fintype State] (q : State) :
    Fin (Fintype.card State + 4) :=
  ⟨(Fintype.equivFin State q).val + 4, by have := (Fintype.equivFin State q).isLt; omega⟩

 noncomputable def translatedAction {k : ℕ} {State : Type} [Fintype State]
    (action : Turing.Action k Bool State) (heads : Fin (k + 3) → Option Bool) :
    Fin (Fintype.card State + 4) × (Fin (k + 3) → Option Bool × Motion) :=
  let im := inputMotion action.inputTape (heads ⟨0, by omega⟩) (heads ⟨k + 2, by omega⟩)
  let next : Fin (Fintype.card State + 4) :=
    match action.state with
    | none => ⟨1, by omega⟩
    | some q' => stateCode q'
  (next, fun i =>
    if hi0 : i.val = 0 then (heads i, im)
    else if hi1 : i.val = 1 then
      match action.output with
      | none => (heads i, .stay)
      | some a => (some a, .right)
    else if him : i.val = k + 2 then (heads i, im)
    else
      let j : Fin k := ⟨i.val - 2, by have := i.isLt; omega⟩
      ((action.workTapes j).1.getD (heads i), Motion.ofSign (action.workTapes j).2))

 /-- Binary fixed-tape implementation of a native binary machine.
 States 0--3 are initialization, first rewind, rewind scan, and halt. -/
 noncomputable def compileMachine {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) : Program where
  states := Fintype.card State + 3
  workTapes := k + 1
  transition := fun q heads =>
    if h0 : q.val = 0 then
      some (stateCode tm.q₀, fun i =>
        if i.val = 0 then (heads i, .stay)
        else if i.val = k + 2 then (some true, .right) else (heads i, .stay))
    else if h1 : q.val = 1 then
      some (⟨2, by omega⟩, fun i => (heads i, if i.val = 1 then .left else .stay))
    else if h2 : q.val = 2 then
      if heads ⟨1, by omega⟩ = none then
        some (⟨3, by omega⟩, fun i => (heads i, if i.val = 1 then .right else .stay))
      else some (⟨2, by omega⟩, fun i => (heads i, if i.val = 1 then .left else .stay))
    else if h3 : q.val = 3 then none
    else
      let native : State := (Fintype.equivFin State).symm
        ⟨q.val - 4, by have := q.isLt; omega⟩
      let action := tm.tr native (heads ⟨0, by omega⟩)
        (fun j => heads ⟨j.val + 2, by have := j.isLt; omega⟩)
      some (translatedAction action heads)

 theorem compile_transition_native {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (q : State) (heads : Fin (k + 3) → Option Bool) :
    (compileMachine tm).transition (stateCode q) heads =
      some (translatedAction (tm.tr q (heads ⟨0, by omega⟩)
        (fun j => heads ⟨j.val + 2, by have := j.isLt; omega⟩)) heads) := by
  have h0 : (stateCode q).val ≠ 0 := by unfold stateCode; simp only; omega
  have h1 : (stateCode q).val ≠ 1 := by unfold stateCode; simp only; omega
  have h2 : (stateCode q).val ≠ 2 := by unfold stateCode; simp only; omega
  have h3 : (stateCode q).val ≠ 3 := by unfold stateCode; simp only; omega
  simp only [compileMachine, h0, h1, h2, h3, ↓reduceDIte]
  congr 3
  simp [stateCode]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main

 theorem Tape.writeMove_keep (s : Tape) : s.writeMove s.head .stay = s := by cases s; rfl

 def Configuration.outputTape {P : Program} (c : Configuration P) : Tape := c.tapes ⟨1, by omega⟩

 def outputStep {P : Program} (c : Configuration P) (q : Fin (P.states + 1)) (m : Motion) : Configuration P :=
  ⟨q, fun i => if i.val = 1 then (c.tapes i).writeMove (c.tapes i).head m else c.tapes i⟩

 theorem outputStep_output {P : Program} (c : Configuration P) (q : Fin (P.states + 1)) (m : Motion) :
    (outputStep c q m).outputTape = c.outputTape.writeMove c.outputTape.head m := by
  simp [outputStep, Configuration.outputTape]

 theorem compile_step_rewind {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (c : Configuration (compileMachine tm))
    (hs : c.state.val = 1) :
    step (compileMachine tm) c = some (outputStep c ⟨2, by simp [compileMachine]⟩ .left) := by
  simp only [step, compileMachine, hs]
  simp only [one_ne_zero, ↓reduceDIte, Option.map_some]
  congr 1
  apply congrArg (Configuration.mk ⟨2, by simp [compileMachine]⟩)
  funext i
  by_cases hi : i.val = 1 <;> simp [outputStep, hi, Tape.writeMove_keep]

 theorem compile_step_scan_blank {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (c : Configuration (compileMachine tm))
    (hs : c.state.val = 2) (hh : c.outputTape.head = none) :
    step (compileMachine tm) c = some (outputStep c ⟨3, by simp [compileMachine]⟩ .right) := by
  simp only [step, compileMachine, hs]
  simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceDIte]
  have hh' : (c.tapes ⟨1, by simp [compileMachine]⟩).head = none := hh
  rw [if_pos hh']
  simp only [Option.map_some]
  congr 1
  apply congrArg (Configuration.mk ⟨3, by simp [compileMachine]⟩)
  funext i
  by_cases hi : i.val = 1 <;> simp [outputStep, hi, Tape.writeMove_keep]

 theorem compile_step_scan_bit {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (c : Configuration (compileMachine tm))
    (hs : c.state.val = 2) (hh : c.outputTape.head ≠ none) :
    step (compileMachine tm) c = some (outputStep c ⟨2, by simp [compileMachine]⟩ .left) := by
  simp only [step, compileMachine, hs]
  simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceDIte]
  have hh' : (c.tapes ⟨1, by simp [compileMachine]⟩).head ≠ none := hh
  rw [if_neg hh']
  simp only [Option.map_some]
  congr 1
  apply congrArg (Configuration.mk ⟨2, by simp [compileMachine]⟩)
  funext i
  by_cases hi : i.val = 1 <;> simp [outputStep, hi, Tape.writeMove_keep]

 theorem compile_step_halt {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (c : Configuration (compileMachine tm))
    (hs : c.state.val = 3) : step (compileMachine tm) c = none := by
  simp [step, compileMachine, hs]

 theorem compile_scan_output {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (L : List Bool) (a : Bool) (R : List (Option Bool))
    (c : Configuration (compileMachine tm)) (hs : c.state.val = 2)
    (ho : c.outputTape = ⟨L.map some, some a, R⟩) :
    ∃ d : Configuration (compileMachine tm),
      execute (compileMachine tm) (L.length + 2) c = d ∧ d.state.val = 3 ∧
      d.outputTape.head :: d.outputTape.right = L.reverse.map some ++ some a :: R := by
  induction L generalizing a R c with
  | nil =>
    let d1 := outputStep c ⟨2, by simp [compileMachine]⟩ .left
    let d2 := outputStep d1 ⟨3, by simp [compileMachine]⟩ .right
    have hc : c.outputTape.head ≠ none := by rw [ho]; simp
    have h1 : step (compileMachine tm) c = some d1 := compile_step_scan_bit tm c hs hc
    have ho1 : d1.outputTape = ⟨[], none, some a :: R⟩ := by
      rw [outputStep_output, ho]
      rfl
    have h2 : step (compileMachine tm) d1 = some d2 :=
      compile_step_scan_blank tm d1 rfl (by rw [ho1])
    refine ⟨d2, ?_, rfl, ?_⟩
    · simp only [List.length_nil, zero_add, execute, h1, h2]
    · rw [outputStep_output, ho1]
      rfl
  | cons b L ih =>
    let d1 := outputStep c ⟨2, by simp [compileMachine]⟩ .left
    have hc : c.outputTape.head ≠ none := by rw [ho]; simp
    have h1 : step (compileMachine tm) c = some d1 := compile_step_scan_bit tm c hs hc
    have ho1 : d1.outputTape = ⟨L.map some, some b, some a :: R⟩ := by
      rw [outputStep_output, ho]
      rfl
    obtain ⟨d, hd, hs3, hout⟩ := ih b (some a :: R) d1 rfl ho1
    refine ⟨d, ?_, hs3, ?_⟩
    · have hlen : (b :: L).length + 2 = (L.length + 2) + 1 := by simp [Nat.add_assoc]
      rw [hlen, execute, h1]
      exact hd
    · simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] using hout

 theorem compile_rewind_output {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (output : List Bool)
    (c : Configuration (compileMachine tm)) (hs : c.state.val = 1)
    (ho : c.outputTape = ⟨output.reverse.map some, none, []⟩) :
    ∃ d : Configuration (compileMachine tm),
      execute (compileMachine tm) (output.length + 2) c = d ∧
      step (compileMachine tm) d = none ∧
      d.outputTape.head :: d.outputTape.right = output.map some ++ [none] := by
  let d1 := outputStep c ⟨2, by simp [compileMachine]⟩ .left
  have h1 : step (compileMachine tm) c = some d1 := compile_step_rewind tm c hs
  cases hr : output.reverse with
  | nil =>
    have he : output = [] := by simpa using congrArg List.reverse hr
    subst output
    have ho1 : d1.outputTape = ⟨[], none, [none]⟩ := by
      rw [outputStep_output, ho]
      rfl
    let d2 := outputStep d1 ⟨3, by simp [compileMachine]⟩ .right
    have h2 : step (compileMachine tm) d1 = some d2 :=
      compile_step_scan_blank tm d1 rfl (by rw [ho1])
    refine ⟨d2, ?_, compile_step_halt tm d2 rfl, ?_⟩
    · simp only [List.length_nil, zero_add, execute, h1, h2]
    · rw [outputStep_output, ho1]
      rfl
  | cons a L =>
    have ho1 : d1.outputTape = ⟨L.map some, some a, [none]⟩ := by
      rw [outputStep_output, ho, hr]
      rfl
    obtain ⟨d, hd, hs3, hout⟩ := compile_scan_output tm L a [none] d1 rfl ho1
    have hlen : output.length = L.length + 1 := by
      have hh := congrArg List.length hr
      simpa only [List.length_reverse, List.length_cons] using hh
    refine ⟨d, ?_, compile_step_halt tm d hs3, ?_⟩
    · have hfuel : output.length + 2 = (L.length + 2) + 1 := by omega
      rw [hfuel, execute, h1]
      exact hd
    · have he : output = L.reverse ++ [a] := by
        have hh := congrArg List.reverse hr
        simpa only [List.reverse_reverse, List.reverse_cons] using hh
      simpa only [he, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] using hout

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main

 def inputContent (input : List Bool) (z : ℤ) : Option Bool :=
  if z ≤ 0 then none else input[(z - 1).toNat]?

 def markerContent (z : ℤ) : Option Bool := if z = 0 then some true else none

 theorem inputContent_nat (input : List Bool) (p : ℕ) (hp : 0 < p) :
    inputContent input (p : ℤ) = input[p - 1]? := by
  have hpos : ¬(p : ℤ) ≤ 0 := by omega
  unfold inputContent
  rw [if_neg hpos]
  congr 1
  omega

 theorem inputContent_native {k : ℕ} {State : Type} {input : List Bool}
    (c : Turing.Cfg k Bool State input) : inputContent input (c.inputPos.val : ℤ) = c.inputSymbol := by
  by_cases h0 : c.inputPos.val = 0
  · rw [Turing.inputSymbol_eq_none_of_boundary (Or.inl h0), h0]
    simp [inputContent]
  · by_cases hr : c.inputPos.val = input.length + 1
    · rw [Turing.inputSymbol_eq_none_of_boundary (Or.inr hr), hr, inputContent_nat _ _ (by omega)]
      simp
    · have hp : c.inputPos.val - 1 < input.length := by have := c.inputPos.isLt; omega
      have hh := Turing.inputSymbolInner (cfg := c) (c.inputPos.val - 1) (by omega) hp
      rw [hh, inputContent_nat _ _ (by omega)]
      simp [hp]

 theorem mapSome_getD (input : List Bool) (i : ℕ) :
    ((input.map some)[i]?).getD none = input[i]? := by
  simp only [List.getElem?_map]
  cases hi : input[i]? <;> rfl

 def initialInputTape (input : List Bool) : Tape :=
  ⟨[], (input.map some).headD none, (input.map some).drop 1⟩

 theorem initialInputTape_represents (input : List Bool) :
    (initialInputTape input).Represents (inputContent input) 1 := by
  intro z
  cases z with
  | ofNat k =>
    cases k with
    | zero =>
      have he : 1 + Int.ofNat 0 = (1 : ℤ) := by decide
      have hc : inputContent input 1 = input[0]? := by
        simpa only [Nat.cast_one, Nat.sub_self] using inputContent_nat input 1 (by omega)
      rw [he, hc]
      cases input <;> rfl
    | succ k =>
      have he : 1 + Int.ofNat (k + 1) = ((k + 2 : ℕ) : ℤ) := by
        simp only [Int.ofNat_eq_natCast]; omega
      rw [he, inputContent_nat input (k + 2) (by omega)]
      simp only [initialInputTape, Tape.readAt, List.getElem?_drop, mapSome_getD]
      congr 1
      omega
  | negSucc k =>
    have hz : 1 + Int.negSucc k ≤ 0 := by omega
    simp only [inputContent, if_pos hz]
    rfl

 theorem initialMarker_represents : (⟨[], some true, []⟩ : Tape).Represents markerContent 0 := by
  intro z
  cases z with
  | ofNat k =>
    cases k with
    | zero => rfl
    | succ k =>
      have hn : (0 : ℤ) + Int.ofNat (k + 1) ≠ 0 := by simp only [Int.ofNat_eq_natCast]; omega
      simp only [markerContent, if_neg hn]
      rfl
  | negSucc k =>
    have hn : (0 : ℤ) + Int.negSucc k ≠ 0 := by omega
    simp only [markerContent, if_neg hn]
    rfl

 theorem initialMarker_after_init : (⟨[some true], none, []⟩ : Tape).Represents markerContent 1 := by
  have h := Tape.represents_move (⟨[], some true, []⟩ : Tape) markerContent 0 initialMarker_represents Motion.right
  simpa [Tape.writeMove, Motion.offset] using h

 theorem inputMotion_matches {k : ℕ} {State : Type} {input : List Bool}
    (c : Turing.Cfg k Bool State input) (s : SignType) :
    ((Turing.moveInputPos c.inputPos s).val : ℤ) =
      (c.inputPos.val : ℤ) + (inputMotion s c.inputSymbol (markerContent (c.inputPos.val : ℤ))).offset := by
  have hv := Turing.val_moveInputPos_eq c.inputPos s
  have hp := c.inputPos.isLt
  cases s with
  | zero => simp [inputMotion, Motion.offset]
  | neg =>
    by_cases h0 : c.inputPos.val = 0
    · simp only [inputMotion, markerContent, h0, Nat.cast_zero, ite_true, Motion.offset]
      simp only [SignType.cast] at hv
      omega
    · have hm : markerContent (c.inputPos.val : ℤ) = none := by
        have hn : (c.inputPos.val : ℤ) ≠ 0 := by omega
        unfold markerContent
        rw [if_neg hn]
      simp only [inputMotion, hm, reduceCtorEq, ite_false, Motion.offset]
      simp only [SignType.cast] at hv
      omega
  | pos =>
    by_cases hr : c.inputPos.val = input.length + 1
    · have hh : c.inputSymbol = none := Turing.inputSymbol_eq_none_of_boundary (Or.inr hr)
      have hm : markerContent (c.inputPos.val : ℤ) = none := by
        have hn : (c.inputPos.val : ℤ) ≠ 0 := by omega
        unfold markerContent
        rw [if_neg hn]
      have hne : (none : Option Bool) ≠ some true := by decide
      simp only [inputMotion, hm, hh, eq_self_iff_true, true_and, if_pos hne, Motion.offset]
      simp only [SignType.cast] at hv
      omega
    · by_cases h0 : c.inputPos.val = 0
      · simp only [inputMotion, markerContent, h0, Nat.cast_zero, ite_true, ne_eq,
          not_true_eq_false, and_false, ite_false, Motion.offset]
        simp only [SignType.cast] at hv
        omega
      · have hi : c.inputPos.val - 1 < input.length := by omega
        have hh := Turing.inputSymbolInner (cfg := c) (c.inputPos.val - 1) (by omega) hi
        simp only [inputMotion, hh, Option.some_ne_none, false_and, ite_false, Motion.offset]
        simp only [SignType.cast] at hv
        omega

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main

 def workIndex {k : ℕ} (i : Fin k) : Fin (k + 3) := ⟨i.val + 2, by have := i.isLt; omega⟩
 def markerIndex (k : ℕ) : Fin (k + 3) := ⟨k + 2, by omega⟩
 def inputIndex (k : ℕ) : Fin (k + 3) := ⟨0, by omega⟩
 def outputIndex (k : ℕ) : Fin (k + 3) := ⟨1, by omega⟩

 noncomputable def nativeControlCode {State : Type} [Fintype State] : Option State → Fin (Fintype.card State + 4)
  | none => ⟨1, by omega⟩
  | some q => stateCode q

 def applyTableAction {P : Program} (c : Configuration P)
    (action : Fin (P.states + 1) × (Fin (P.workTapes + 2) → Option Bool × Motion)) : Configuration P :=
  ⟨action.1, fun i => (c.tapes i).writeMove (action.2 i).1 (action.2 i).2⟩

 theorem step_eq_applyTableAction {P : Program} (c : Configuration P)
    (action : Fin (P.states + 1) × (Fin (P.workTapes + 2) → Option Bool × Motion))
    (ha : P.transition c.state (fun i => (c.tapes i).head) = some action) :
    step P c = some (applyTableAction c action) := by
  simp only [step, ha, Option.map_some, applyTableAction]

 theorem translatedAction_state {k : ℕ} {State : Type} [Fintype State]
    (a : Turing.Action k Bool State) (heads : Fin (k + 3) → Option Bool) :
    (translatedAction a heads).1 = nativeControlCode a.state := rfl

 theorem translatedAction_input {k : ℕ} {State : Type} [Fintype State]
    (a : Turing.Action k Bool State) (heads : Fin (k + 3) → Option Bool) :
    (translatedAction a heads).2 (inputIndex k) =
      (heads (inputIndex k), inputMotion a.inputTape (heads (inputIndex k)) (heads (markerIndex k))) := by
  simp [translatedAction, inputIndex, markerIndex]

 theorem translatedAction_marker {k : ℕ} {State : Type} [Fintype State]
    (a : Turing.Action k Bool State) (heads : Fin (k + 3) → Option Bool) :
    (translatedAction a heads).2 (markerIndex k) =
      (heads (markerIndex k), inputMotion a.inputTape (heads (inputIndex k)) (heads (markerIndex k))) := by
  simp [translatedAction, inputIndex, markerIndex]

 theorem translatedAction_work {k : ℕ} {State : Type} [Fintype State]
    (a : Turing.Action k Bool State) (heads : Fin (k + 3) → Option Bool) (i : Fin k) :
    (translatedAction a heads).2 (workIndex i) =
      ((a.workTapes i).1.getD (heads (workIndex i)), Motion.ofSign (a.workTapes i).2) := by
  have h0 : i.val + 2 ≠ 0 := by omega
  have h1 : i.val + 2 ≠ 1 := by omega
  have hm : i.val + 2 ≠ k + 2 := by have := i.isLt; omega
  have hne : i.val ≠ k := by have := i.isLt; omega
  simp [translatedAction, workIndex, h0, h1, hm, hne]

 theorem translatedAction_output {k : ℕ} {State : Type} [Fintype State]
    (a : Turing.Action k Bool State) (heads : Fin (k + 3) → Option Bool) :
    (translatedAction a heads).2 (outputIndex k) =
      match a.output with
      | none => (heads (outputIndex k), Motion.stay)
      | some b => (some b, Motion.right) := by
  cases ho : a.output <;> simp [translatedAction, outputIndex, ho]

 def MachineSimulation {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) {input : List Bool}
    (native : Turing.Cfg k Bool State input) (c : Configuration (compileMachine tm)) : Prop :=
  c.state = nativeControlCode native.state ∧
  (∀ i : Fin k, (c.tapes (workIndex i)).Represents (native.workTapes i) (native.workTapePos i)) ∧
  (c.tapes (inputIndex k)).Represents (inputContent input) (native.inputPos.val : ℤ) ∧
  (c.tapes (markerIndex k)).Represents markerContent (native.inputPos.val : ℤ) ∧
  c.outputTape = ⟨native.output.reverse.map some, none, []⟩

 theorem Tape.represents_head (s : Tape) (w : ℤ → Option Bool) (p : ℤ) (hs : s.Represents w p) :
    s.head = w p := by simpa only [Tape.readAt_zero, add_zero] using hs 0

 theorem Tape.represents_optional_write {s : Tape} {w : ℤ → Option Bool} {p : ℤ}
    (hs : s.Represents w p) (a : Option (Option Bool)) (m : Motion) :
    (s.writeMove (a.getD s.head) m).Represents
      (match a with | none => w | some b => Function.update w p b) (p + m.offset) := by
  cases a with
  | none => exact s.represents_move w p hs m
  | some b => exact s.represents_writeMove w p hs b m

 noncomputable def initializedMachine {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (input : List Bool) : Configuration (compileMachine tm) :=
  ⟨stateCode tm.q₀, fun i =>
    if i.val = 0 then initialInputTape input
    else if i.val = k + 2 then ⟨[some true], none, []⟩ else ⟨[], none, []⟩⟩

 theorem compile_initial_step {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (input : List Bool) :
    step (compileMachine tm) (initial (compileMachine tm) input) = some (initializedMachine tm input) := by
  simp only [step, initial, compileMachine]
  simp only [Fin.val_zero, ↓reduceDIte, Option.map_some]
  congr 1
  unfold initializedMachine
  apply congrArg (@Configuration.mk (compileMachine tm) (stateCode tm.q₀))
  funext i
  by_cases h0 : i.val = 0
  · simp [initializedMachine, h0, initialInputTape, Tape.writeMove]
  · by_cases hm : i.val = k + 2
    · simp [initializedMachine, h0, hm, Tape.writeMove]
    · simp [initializedMachine, h0, hm, Tape.writeMove]

 theorem compile_initial_simulation {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (input : List Bool) :
    MachineSimulation tm (tm.initCfg input) (initializedMachine tm input) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro i
    have h0 : i.val + 2 ≠ 0 := by omega
    have hm : i.val ≠ k := by have := i.isLt; omega
    simpa [initializedMachine, workIndex, h0, hm, Turing.MultiTapeNTM.initCfg, Turing.Cfg.init] using
      Tape.represents_blank 0
  · simpa [initializedMachine, inputIndex, Turing.MultiTapeNTM.initCfg, Turing.Cfg.init] using
      initialInputTape_represents input
  · simpa [initializedMachine, markerIndex, Turing.MultiTapeNTM.initCfg, Turing.Cfg.init] using
      initialMarker_after_init
  · simp [initializedMachine, Configuration.outputTape, Turing.MultiTapeNTM.initCfg, Turing.Cfg.init]

 theorem compile_live_step {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) {input : List Bool}
    (native : Turing.Cfg k Bool State input) (c : Configuration (compileMachine tm))
    (hr : MachineSimulation tm native c) (q : State) (hq : native.state = some q) :
    ∃ d : Configuration (compileMachine tm), step (compileMachine tm) c = some d ∧
      MachineSimulation tm (tm.step native) d := by
  obtain ⟨hstate, hwork, hinput, hmarker, houtput⟩ := hr
  have hcs : c.state = stateCode q := by simpa only [hq, nativeControlCode] using hstate
  let heads := fun i => (c.tapes i).head
  have hI : heads (inputIndex k) = native.inputSymbol :=
    (Tape.represents_head _ _ _ hinput).trans (inputContent_native native)
  have hM : heads (markerIndex k) = markerContent (native.inputPos.val : ℤ) :=
    Tape.represents_head _ _ _ hmarker
  have hIr : (c.tapes (inputIndex k)).head = native.inputSymbol := hI
  have hMr : (c.tapes (markerIndex k)).head = markerContent (native.inputPos.val : ℤ) := hM
  have hW (i : Fin k) : heads (workIndex i) = native.workTapeSymbols i := Tape.represents_head _ _ _ (hwork i)
  let a := tm.tr q native.inputSymbol native.workTapeSymbols
  let d := applyTableAction c (translatedAction a heads)
  have ha : (compileMachine tm).transition c.state heads = some (translatedAction a heads) := by
    rw [hcs, compile_transition_native]
    change some (translatedAction (tm.tr q (heads (inputIndex k)) (fun i => heads (workIndex i))) heads) = _
    rw [hI]
    have he : (fun i => heads (workIndex i)) = native.workTapeSymbols := funext hW
    rw [he]
  refine ⟨d, step_eq_applyTableAction c _ ha, ?_⟩
  rw [Turing.MultiTapeTM.step_of_state hq]
  change MachineSimulation tm (a.apply native) d
  refine ⟨translatedAction_state a heads, ?_, ?_, ?_, ?_⟩
  · intro i
    have hh := Tape.represents_optional_write (hwork i) (a.workTapes i).1 (Motion.ofSign (a.workTapes i).2)
    cases hw : (a.workTapes i).1 with
    | none => simpa only [d, applyTableAction, translatedAction_work, Motion.offset_ofSign,
        Turing.Action.apply, heads, hw] using hh
    | some b => simpa only [d, applyTableAction, translatedAction_work, Motion.offset_ofSign,
        Turing.Action.apply, heads, hw] using hh
  · have hh := Tape.represents_move _ _ _ hinput
      (inputMotion a.inputTape native.inputSymbol (markerContent (native.inputPos.val : ℤ)))
    simpa only [d, applyTableAction, translatedAction_input, heads, hIr, hMr, Turing.Action.apply,
      inputMotion_matches] using hh
  · have hh := Tape.represents_move _ _ _ hmarker
      (inputMotion a.inputTape native.inputSymbol (markerContent (native.inputPos.val : ℤ)))
    simpa only [d, applyTableAction, translatedAction_marker, heads, hIr, hMr, Turing.Action.apply,
      inputMotion_matches] using hh
  · change (c.tapes (outputIndex k)).writeMove ((translatedAction a heads).2 (outputIndex k)).1
      ((translatedAction a heads).2 (outputIndex k)).2 = _
    rw [translatedAction_output]
    cases ho : a.output with
    | none =>
      simp only [ho, Tape.writeMove_keep, Turing.Action.apply, Option.toList_none, List.append_nil]
      exact houtput
    | some b =>
      change c.outputTape.writeMove (some b) Motion.right = _
      rw [houtput]
      simp [Turing.Action.apply, ho, Tape.writeMove, List.reverse_append, List.map_append]

end EditGV897.Main

namespace EditGV897.Main

 theorem execute_eq_of_halt (P : Program) (c : Configuration P) (hs : step P c = none) (fuel : ℕ) :
    execute P fuel c = c := by
  cases fuel with
  | zero => rfl
  | succ k => simp only [execute, hs]

 theorem execute_add (P : Program) (a b : ℕ) (c : Configuration P) :
    execute P (a + b) c = execute P b (execute P a c) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, execute]
  | succ a ih =>
    cases hs : step P c with
    | none => simp only [execute_eq_of_halt P c hs]
    | some c' =>
      rw [Nat.succ_add]
      simp only [execute, hs]
      exact ih c'

 theorem Runs.mono {P : Program} {input output : List Bool} {s t : ℕ}
    (h : Runs P input output s) (hst : s ≤ t) : Runs P input output t := by
  obtain ⟨k, hk, c, hc, hhalt, hout⟩ := h
  exact ⟨k, hk.trans hst, c, hc, hhalt, hout⟩

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main

 theorem compile_simulate_prefix {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (input : List Bool) (N : ℕ)
    (hlive : ∀ i : ℕ, i < N → (tm.runFrom (tm.initCfg input) i).state ≠ none) :
    ∃ c : Configuration (compileMachine tm),
      execute (compileMachine tm) (N + 1) (initial (compileMachine tm) input) = c ∧
      MachineSimulation tm (tm.runFrom (tm.initCfg input) N) c := by
  induction N with
  | zero =>
    refine ⟨initializedMachine tm input, ?_, compile_initial_simulation tm input⟩
    simp only [execute, compile_initial_step]
  | succ N ih =>
    obtain ⟨c, hc, hr⟩ := ih (fun i hi => hlive i (by omega))
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive N (by omega))
    obtain ⟨d, hd, hr'⟩ := compile_live_step tm (tm.runFrom (tm.initCfg input) N) c hr q hq
    refine ⟨d, ?_, ?_⟩
    · rw [execute_add (compileMachine tm) (N + 1) 1, hc]
      simp only [execute, hd]
    · simpa only [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply'] using hr'

 theorem compile_computes {k : ℕ} {State : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) {input output : List Bool} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s) :
    Runs (compileMachine tm) input output (2 * t + 3) := by
  classical
  have hhalt : (tm.runFrom (tm.initCfg input) t).state = none :=
    Turing.MultiTapeTM.runsInTime_iff_halted.mp h.2.1
  have hex : ∃ τ : ℕ, (tm.runFrom (tm.initCfg input) τ).state = none := ⟨t, hhalt⟩
  let τ := Nat.find hex
  have hτ : (tm.runFrom (tm.initCfg input) τ).state = none := Nat.find_spec hex
  have hτt : τ ≤ t := Nat.find_min' hex hhalt
  have hlive : ∀ i : ℕ, i < τ → (tm.runFrom (tm.initCfg input) i).state ≠ none :=
    fun i hi => Nat.find_min hex hi
  obtain ⟨u, hu, hout⟩ := h.1
  have hτu : τ ≤ u := Nat.find_min' hex hu
  have heq := Turing.MultiTapeTM.runFrom_eq_of_halt tm (tm.initCfg input) hτu hτ
  have houtτ : (tm.runFrom (tm.initCfg input) τ).output = output := by
    rw [← heq]
    exact hout
  obtain ⟨c, hc, hr⟩ := compile_simulate_prefix tm input τ hlive
  have hs : c.state.val = 1 := by rw [hr.1, hτ]; rfl
  have ho : c.outputTape = ⟨output.reverse.map some, none, []⟩ := by rw [hr.2.2.2.2, houtτ]
  obtain ⟨d, hd, hdone, houtd⟩ := compile_rewind_output tm output c hs ho
  have hlen : output.length ≤ t := h.length_output_le
  refine ⟨(τ + 1) + (output.length + 2), by omega, d, ?_, hdone, houtd⟩
  rw [execute_add, hc, hd]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main

 theorem program_of_polytime {α β : Type*} (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f encIn encOut) :
    ∃ (P : Program) (A d : ℕ), 0 < A ∧ ∀ a : α,
      Runs P (encIn a) (encOut (f a)) (polyBudget A d (encIn a).length) ∧
      (encOut (f a)).length ≤ polyBudget A d (encIn a).length := by
  classical
  obtain ⟨t, s, ht, _, k, State, hfinite, tm, htm⟩ := hf
  letI : Finite State := hfinite
  letI : Fintype State := Fintype.ofFinite State
  obtain ⟨c, d, htime⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  refine ⟨compileMachine tm, 2 * c + 3, d, by omega, ?_⟩
  intro a
  have hp : 1 ≤ ((encIn a).length + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hb : 2 * t (encIn a).length + 3 ≤ polyBudget (2 * c + 3) d (encIn a).length := by
    unfold polyBudget
    nlinarith [htime (encIn a).length]
  refine ⟨(compile_computes tm (htm a)).mono hb, ?_⟩
  have ho := (htm a).length_output_le
  change (encOut (f a)).length ≤ t (encIn a).length at ho
  omega

 theorem program_of_tidy_polytime {α β : Type*} (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (hf : Turing.MultiTapeTM.ComputableTidilyInPolyTime f encIn encOut) :
    ∃ (P : Program) (A d : ℕ), 0 < A ∧ ∀ a : α,
      Runs P (encIn a) (encOut (f a)) (polyBudget A d (encIn a).length) ∧
      (encOut (f a)).length ≤ polyBudget A d (encIn a).length :=
  program_of_polytime f encIn encOut hf.computableInPolyTime

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev RawEquation := List Bool × Bool

abbrev rawEquationEncoding : RawEquation ↪ List Bool := encPair encBits encBool

def rawXorEquation (a b : RawEquation) : RawEquation :=
  (a.1.zipWith Bool.xor b.1, Bool.xor a.2 b.2)

def rawCoordinate (e : RawEquation) (k : ℕ) : Bool := e.1[k]?.getD false

def rawZero (e : RawEquation) : Bool := !(e.1.any id)

@[fun_prop]
theorem rawXorEquation_polytime : ComputableTidilyInPolyTime
    (fun p : RawEquation × RawEquation => rawXorEquation p.1 p.2)
    (encPair rawEquationEncoding rawEquationEncoding) rawEquationEncoding := by
  let left := fst rawEquationEncoding rawEquationEncoding
  let right := snd rawEquationEncoding rawEquationEncoding
  have hl := (fst encBits encBool).comp left
  have hr := (fst encBits encBool).comp right
  have hbl := (snd encBits encBool).comp left
  have hbr := (snd encBits encBool).comp right
  have hxor : ComputableTidilyInPolyTime (fun p : Bool × Bool => Bool.xor p.1 p.2)
      (encPair encBool encBool) encBool := of_finite _
  exact ((bitsZipWith Bool.xor).comp (hl.prod hr)).prod (hxor.comp (hbl.prod hbr))

@[fun_prop]
theorem rawCoordinate_polytime : ComputableTidilyInPolyTime
    (fun p : RawEquation × ℕ => rawCoordinate p.1 p.2)
    (encPair rawEquationEncoding encUnary) encBool := by
  have hl := (fst encBits encBool).comp (fst rawEquationEncoding encUnary)
  have hi := snd rawEquationEncoding encUnary
  have hg := bitsGetElem? hl hi
  have hd : ComputableTidilyInPolyTime (fun a : Option Bool => a.getD false) (encOption encBool) encBool :=
    of_finite _
  exact hd.comp hg

@[fun_prop]
theorem rawZero_polytime : ComputableTidilyInPolyTime rawZero rawEquationEncoding encBool := by
  have ha := bitsAnyWithInput (test := fun _ b => b) (fst encBits encBool) (snd rawEquationEncoding encBool)
  have hn : ComputableTidilyInPolyTime Bool.not encBool encBool := of_finite _
  exact hn.comp ha

theorem listErase_polytime {α : Type} [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : List α × α => p.1.erase p.2)
      (encPair (encList enc) enc) (encList enc) := by
  have hl := fst (encList enc) enc
  have hv := snd (encList enc) enc
  have hi := idxOfWithInput hl hv
  have hs := unary_add.comp (hi.prod (const (encMid := encUnary) 1))
  have ht := listTakeWithInput hl hi
  have hd := listDropWithInput hl hs
  convert listAppend' ht hd using 1
  funext p
  dsimp only [Function.comp_def]
  rw [← List.eraseIdx_eq_take_drop_succ, List.eraseIdx_idxOf_eq_erase]

abbrev RawEliminationState := ℕ × (ℕ × List RawEquation)
abbrev rawStateEncoding := encPair encUnary (encPair encUnary (encList rawEquationEncoding))

def rawPivot (k : ℕ) (E : List RawEquation) : Option RawEquation :=
  E.find? (fun e => rawCoordinate e k)

def rawClear (k : ℕ) (E : List RawEquation) (pivot : RawEquation) : List RawEquation :=
  (@List.erase RawEquation instBEqOfDecidableEq E pivot).map (fun e => if rawCoordinate e k then rawXorEquation e pivot else e)

def rawEliminationStep (s : RawEliminationState) : RawEliminationState :=
  let p := rawPivot s.1 s.2.2
  (s.1 + 1, if p.isSome then
    (s.2.1 + 1, rawClear s.1 s.2.2 (p.getD ([], false))) else s.2)

@[fun_prop]
theorem rawPivot_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List RawEquation => rawPivot p.1 p.2)
    (encPair encUnary (encList rawEquationEncoding)) (encOption rawEquationEncoding) := by
  apply findWithInput (snd encUnary (encList rawEquationEncoding))
  exact rawCoordinate_polytime.comp ((snd _ _).prod ((fst _ _).fst'))

@[fun_prop]
theorem rawClear_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawEquation) × RawEquation => rawClear p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary (encList rawEquationEncoding)) rawEquationEncoding)
    (encList rawEquationEncoding) := by
  unfold rawClear
  have he := listErase_polytime rawEquationEncoding
  let en := encPair encUnary (encList rawEquationEncoding)
  have hfirst := fst en rawEquationEncoding
  have hsecond := snd en rawEquationEncoding
  have hl := he.comp (hfirst.snd'.prod hsecond)
  have houter := fst (encPair en rawEquationEncoding) rawEquationEncoding
  have helem := snd (encPair en rawEquationEncoding) rawEquationEncoding
  have hc := rawCoordinate_polytime.comp (helem.prod houter.fst'.fst')
  have hx := rawXorEquation_polytime.comp (helem.prod houter.snd')
  simpa only [Function.comp_def] using mapWithInput (encB := rawEquationEncoding)
    (f := fun (p : (ℕ × List RawEquation) × RawEquation) (e : RawEquation) =>
      if rawCoordinate e p.1.1 then rawXorEquation e p.2 else e)
    hl (by simpa only [Function.comp_def] using hc.cond hx helem)

@[fun_prop]
theorem rawEliminationStep_polytime : ComputableTidilyInPolyTime rawEliminationStep
    rawStateEncoding rawStateEncoding := by
  unfold rawEliminationStep
  have hk := fst encUnary (encPair encUnary (encList rawEquationEncoding))
  have hs := snd encUnary (encPair encUnary (encList rawEquationEncoding))
  have hr := hs.fst'
  have he := hs.snd'
  have hp := rawPivot_polytime.comp (hk.prod he)
  have hd := optionGetDWithInput hp (const (encMid := rawEquationEncoding) ([], false))
  have hc := rawClear_polytime.comp ((hk.prod he).prod hd)
  exact (unary_add.comp (hk.prod (const (encMid := encUnary) 1))).pair
    (hp.optionIsSome.cond ((unary_add.comp (hr.prod (const (encMid := encUnary) 1))).prod hc) hs)

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

theorem rawClear_size (k : ℕ) (E : List RawEquation) (p : RawEquation) :
    (encList rawEquationEncoding (rawClear k E p)).length ≤
      (encList rawEquationEncoding E).length := by
  letI : BEq RawEquation := instBEqOfDecidableEq
  unfold rawClear
  refine (length_encList_map_le rawEquationEncoding rawEquationEncoding ?_).trans
    (length_encList_sublist rawEquationEncoding (by exact List.erase_sublist))
  intro e he
  split
  · simp only [rawXorEquation, rawEquationEncoding, length_encPair,
      encBits_apply, encBool_apply, List.length_singleton, List.length_zipWith]
    omega
  · exact le_rfl

theorem rawEliminationStep_growth (s : RawEliminationState) :
    (rawStateEncoding (rawEliminationStep s)).length ≤ (rawStateEncoding s).length + 4 := by
  dsimp only [rawEliminationStep]
  split
  · have h := rawClear_size s.1 s.2.2 ((rawPivot s.1 s.2.2).getD ([], false))
    simp only [rawStateEncoding, length_encPair, encUnary_apply, List.length_replicate,
      Prod.fst, Prod.snd]
    omega
  · simp only [rawStateEncoding, length_encPair, encUnary_apply, List.length_replicate,
      Prod.fst, Prod.snd]
    omega

def rawEliminate (n : ℕ) (E : List RawEquation) : RawEliminationState :=
  rawEliminationStep^[n] (0, (0, E))

@[fun_prop]
theorem rawEliminate_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List RawEquation => rawEliminate p.1 p.2)
    (encPair encUnary (encList rawEquationEncoding)) rawStateEncoding := by
  exact iterate_of_bounded_growth (fst _ _)
    ((const (encMid := encUnary) 0).prod
      ((const (encMid := encUnary) 0).prod (snd _ _)))
    rawEliminationStep_polytime rawEliminationStep_growth

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawBad (e : RawEquation) : Bool := rawZero e && e.2

def rawPivotCount (E : List RawEquation) : ℕ := (E.filter (fun e => !rawZero e)).length

def rawGaussian : ℕ → ℕ → List RawEquation → List RawEquation
  | 0, _, E => E
  | fuel + 1, k, E => match rawPivot k E with
    | none => rawGaussian fuel (k+1) E
    | some p => p :: rawGaussian fuel (k+1) (rawClear k E p)

def rawSummary (s : RawEliminationState) : ℕ × Bool :=
  (s.2.1 + rawPivotCount s.2.2, s.2.2.any rawBad)

theorem rawCoordinate_nonzero (e : RawEquation) (k : ℕ) (h : rawCoordinate e k = true) :
    rawZero e = false := by
  unfold rawCoordinate at h
  have hm : true ∈ e.1 := by
    cases he : e.1[k]? with
    | none => simp [he] at h
    | some b =>
      have hb : b = true := by simpa only [he, Option.getD_some] using h
      exact hb ▸ List.mem_of_getElem? he
  have ha : e.1.any id = true := List.any_eq_true.mpr ⟨true, hm, rfl⟩
  simp [rawZero, ha]

theorem rawGaussian_summary (fuel : ℕ) (s : RawEliminationState) :
    rawSummary (rawEliminationStep^[fuel] s) =
      (s.2.1 + rawPivotCount (rawGaussian fuel s.1 s.2.2),
        (rawGaussian fuel s.1 s.2.2).any rawBad) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply, ih]
    cases hp : rawPivot s.1 s.2.2 with
    | none => simp [rawEliminationStep, hp, rawGaussian]
    | some p =>
      have hcoord : rawCoordinate p s.1 = true :=
        List.find?_some (p := fun e : RawEquation => rawCoordinate e s.1) hp
      have hz : rawZero p = false := rawCoordinate_nonzero p s.1 hcoord
      simp [rawEliminationStep, hp, rawGaussian, rawPivotCount, rawBad, hz,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[fun_prop]
theorem rawBad_polytime : ComputableTidilyInPolyTime rawBad rawEquationEncoding encBool := by
  have hand : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 && p.2)
      (encPair encBool encBool) encBool := of_finite _
  exact hand.comp (rawZero_polytime.prod (snd encBits encBool))

@[fun_prop]
theorem rawPivotCount_polytime : ComputableTidilyInPolyTime rawPivotCount
    (encList rawEquationEncoding) encUnary := by
  unfold rawPivotCount
  apply length_list rawEquationEncoding |>.comp
  apply filterWithInput (id' (encIn := encList rawEquationEncoding))
  have hn : ComputableTidilyInPolyTime Bool.not encBool encBool := of_finite _
  exact hn.comp (rawZero_polytime.comp (snd _ _))

@[fun_prop]
theorem rawSummary_polytime : ComputableTidilyInPolyTime rawSummary
    rawStateEncoding (encPair encUnary encBool) := by
  have hs := snd encUnary (encPair encUnary (encList rawEquationEncoding))
  have hr := hs.fst'
  have he := hs.snd'
  have hc := rawPivotCount_polytime.comp he
  have ha := anyWithInput (test := fun _ e => rawBad e) he
    (rawBad_polytime.comp (snd _ _))
  exact (unary_add.comp (hr.prod hc)).prod ha

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main

def bitBool (a : Bit) : Bool := decide (a ≠ 0)

@[simp] theorem bitBool_zero : bitBool 0 = false := by decide
@[simp] theorem bitBool_one : bitBool 1 = true := by decide

theorem bitBool_injective : Function.Injective bitBool := by
  intro a b
  fin_cases a <;> fin_cases b <;> norm_num [bitBool]

@[simp] theorem bitBool_add (a b : Bit) : bitBool (a+b) = Bool.xor (bitBool a) (bitBool b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem wordCode_injective {n : ℕ} : Function.Injective (@wordCode n) := by
  intro x y h
  have hw : wordList x = wordList y := (List.map_inj_right bitBool_injective).mp h
  simpa only [listWord_wordList] using congrArg (listWord n) hw

@[simp] theorem wordCode_length {n : ℕ} (x : Word n) : (wordCode x).length = n := by
  simp [wordCode, bitCode]

@[simp] theorem wordCode_get {n : ℕ} (x : Word n) (i : Fin n) :
    (wordCode x)[i.val]? = some (bitBool (x i)) := by
  simp [wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters, bitBool]

@[simp] theorem wordCode_add {n : ℕ} (x y : Word n) :
    wordCode (x+y) = (wordCode x).zipWith Bool.xor (wordCode y) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [wordCode_length] at hi
    have heq := bitBool_add (x ⟨i, hi⟩) (y ⟨i, hi⟩)
    simpa [wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters,
      List.getElem_zipWith, bitBool] using heq

def rawEquation {n : ℕ} (e : Equation n) : EditGV897.Runtime.RawEquation :=
  (wordCode e.1, bitBool e.2)

theorem rawEquation_injective {n : ℕ} : Function.Injective (@rawEquation n) := by
  intro a b h
  exact Prod.ext (wordCode_injective (congrArg Prod.fst h))
    (bitBool_injective (congrArg Prod.snd h))

@[simp] theorem rawEquation_xor {n : ℕ} (a b : Equation n) :
    rawEquation (xorEquation a b) = EditGV897.Runtime.rawXorEquation (rawEquation a) (rawEquation b) := by
  simp [rawEquation, xorEquation, EditGV897.Runtime.rawXorEquation]

@[simp] theorem rawEquation_coordinate {n k : ℕ} (e : Equation n) (hk : k < n) :
    EditGV897.Runtime.rawCoordinate (rawEquation e) k = decide (e.1 ⟨k, hk⟩ ≠ 0) := by
  change (wordCode e.1)[k]?.getD false = bitBool (e.1 ⟨k, hk⟩)
  rw [wordCode_get e.1 ⟨k, hk⟩]
  rfl

@[simp] theorem rawEquation_zero {n : ℕ} (e : Equation n) :
    EditGV897.Runtime.rawZero (rawEquation e) = decide (e.1 = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [EditGV897.Runtime.rawZero, rawEquation, Bool.not_eq_true',
    List.any_eq_false, wordCode, bitCode, List.forall_mem_map, bitBool,
    decide_eq_false_iff_not, ne_eq, not_not, decide_eq_true_eq]
  constructor
  · intro h
    funext i
    simpa using h (e.1 i) (by simp [wordList, DeletionHash.MixedEdit.letters])
  · intro h
    simp [h, wordList, DeletionHash.MixedEdit.letters]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawCount (n : ℕ) (E : List RawEquation) : ℕ :=
  let result := rawSummary (rawEliminate n E)
  if result.2 then 0 else 2 ^ (n - result.1)

@[fun_prop]
theorem rawCount_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List RawEquation => rawCount p.1 p.2)
    (encPair encUnary (encList rawEquationEncoding)) encNat := by
  unfold rawCount
  have hr := rawSummary_polytime.comp rawEliminate_polytime
  have hn := fst encUnary (encList rawEquationEncoding)
  have he := unary_sub.comp (hn.prod hr.fst')
  exact hr.snd'.cond (const 0) (binary_two_pow.comp he)

def readUnary (w : List Bool) : ℕ := w.idxOf false

def dropHeader (w : List Bool) : List Bool := w.drop (readUnary w + 1)

@[fun_prop]
theorem readUnary_polytime : ComputableTidilyInPolyTime readUnary encBits encUnary := by
  exact idxOfWithInput bitsToList (const false)

@[fun_prop]
theorem dropHeader_polytime : ComputableTidilyInPolyTime dropHeader encBits encBits := by
  unfold dropHeader
  exact bitsDropWithInput id' (unary_add.comp (readUnary_polytime.prod (const (encMid := encUnary) 1)))

/-- A bounded total parser: malformed data is truncated or padded by zero bits. -/
def rawReadEquation (n : ℕ) (w : List Bool) : RawEquation :=
  (w.take n, w[n]?.getD false)

@[fun_prop]
theorem rawReadEquation_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool => rawReadEquation p.1 p.2)
    (encPair encUnary encBits) rawEquationEncoding := by
  exact (bitsTakeWithInput (snd _ _) (fst _ _)).prod
    (by simpa only [List.getD_eq_getElem?_getD] using bitsGetDWithInput (snd encUnary encBits) (fst encUnary encBits) false)

/-- Parse a fixed number of dense equations of a declared common width. -/
def rawReadEquations (n m : ℕ) (w : List Bool) : List RawEquation :=
  (List.range m).map (fun i => rawReadEquation n (w.drop (i * (n+1))))

@[fun_prop]
theorem rawReadEquations_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × List Bool => rawReadEquations p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encBits) (encList rawEquationEncoding) := by
  unfold rawReadEquations
  have hlist := range.comp ((fst (encPair encUnary encUnary) encBits).snd')
  apply mapWithInput (encB := rawEquationEncoding) hlist
  have houter := fst (encPair (encPair encUnary encUnary) encBits) encUnary
  have hi := snd (encPair (encPair encUnary encUnary) encBits) encUnary
  have hn := houter.fst'.fst'
  have hw := houter.snd'
  exact rawReadEquation_polytime.comp (hn.prod
    (bitsDropWithInput hw (unary_mul.comp (hi.prod
      (unary_add.comp (hn.prod (const (encMid := encUnary) 1)))))))

def rawCounter (w : List Bool) : ℕ :=
  let n := readUnary w
  let w' := dropHeader w
  let m := readUnary w'
  rawCount n (rawReadEquations n m (dropHeader w'))

@[fun_prop]
theorem rawCounter_polytime : ComputableTidilyInPolyTime rawCounter encBits encNat := by
  unfold rawCounter
  have hn := readUnary_polytime
  have hw := dropHeader_polytime
  have hm := readUnary_polytime.comp hw
  have hw' := dropHeader_polytime.comp hw
  exact rawCount_polytime.comp
    (hn.prod (rawReadEquations_polytime.comp ((hn.prod hm).prod hw')))

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

theorem rawPivot_equations {n k : ℕ} (E : List (Equation n)) (hk : k < n) :
    rawPivot k (E.map rawEquation) =
      (E.find? (fun e => decide (e.1 ⟨k, hk⟩ ≠ 0))).map rawEquation := by
  simp [rawPivot, List.find?_map, Function.comp_def, rawEquation_coordinate, hk]

theorem rawClear_equations {n k : ℕ} (E : List (Equation n)) (p : Equation n) (hk : k < n) :
    rawClear k (E.map rawEquation) (rawEquation p) =
      ((E.erase p).map (fun e => if e.1 ⟨k, hk⟩ = 0 then e else xorEquation e p)).map rawEquation := by
  letI : BEq RawEquation := instBEqOfDecidableEq
  unfold rawClear
  rw [← List.map_erase rawEquation_injective]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro e he
  rw [rawEquation_coordinate e hk]
  by_cases hz : e.1 ⟨k, hk⟩ = 0 <;> simp [hz]

theorem rawGaussian_equations {n : ℕ} (fuel k : ℕ) (E : List (Equation n))
    (h : fuel + k ≤ n) :
    rawGaussian fuel k (E.map rawEquation) = (gaussian fuel k E).map rawEquation := by
  induction fuel generalizing k E with
  | zero => rfl
  | succ fuel ih =>
    have hk : k < n := by omega
    unfold rawGaussian gaussian
    rw [dif_pos hk, rawPivot_equations E hk]
    cases hp : E.find? (fun e => decide (e.1 ⟨k, hk⟩ ≠ 0)) with
    | none =>
      simp only [Option.map_none]
      exact ih (k+1) E (by omega)
    | some p =>
      simp only [Option.map_some, List.map_cons]
      rw [rawClear_equations E p hk, ih (k+1) _ (by omega)]

theorem rawPivotCount_equations {n : ℕ} (E : List (Equation n)) :
    rawPivotCount (E.map rawEquation) = pivotCount E := by
  unfold rawPivotCount pivotCount
  rw [List.filter_map]
  simp [Function.comp_def, rawEquation_zero]

theorem rawBad_equations {n : ℕ} (E : List (Equation n)) :
    (E.map rawEquation).any rawBad = E.any (fun e => decide (e.1 = 0 ∧ e.2 ≠ 0)) := by
  simp only [List.any_map]
  congr 1
  funext e
  dsimp only [Function.comp_def]
  unfold rawBad
  rw [rawEquation_zero]
  simp [rawEquation, bitBool]

theorem rawCount_equations {n : ℕ} (E : List (Equation n)) :
    rawCount n (E.map rawEquation) = affineCount E := by
  unfold rawCount rawEliminate
  rw [rawGaussian_summary n (0, (0, E.map rawEquation)),
    rawGaussian_equations n 0 E (by omega)]
  simp only [Nat.zero_add, rawPivotCount_equations, rawBad_equations, affineCount]

@[simp] theorem readUnary_prefix (n : ℕ) (w : List Bool) :
    readUnary (unary n ++ w) = n := by
  induction n with
  | zero => simp [unary, readUnary]
  | succ n ih =>
    have he : unary (n+1) ++ w = true :: (unary n ++ w) := by simp [unary, List.replicate_succ]
    rw [he]
    simpa [readUnary, List.idxOf_cons] using ih

@[simp] theorem dropHeader_prefix (n : ℕ) (w : List Bool) :
    dropHeader (unary n ++ w) = w := by
  unfold dropHeader
  rw [readUnary_prefix]
  simp [unary, List.drop_append]

@[simp] theorem rawReadEquation_code {n : ℕ} (e : Equation n) (tail : List Bool) :
    rawReadEquation n (wordCode e.1 ++ bitBool e.2 :: tail) = rawEquation e := by
  simp [rawReadEquation, rawEquation, List.take_append, List.getElem?_append_right,
    wordCode_length, List.take_of_length_le]

theorem rawReadEquations_codes {n : ℕ} (E : List (Equation n)) :
    rawReadEquations n E.length
      (E.flatMap (fun e => wordCode e.1 ++ [bitBool e.2])) = E.map rawEquation := by
  induction E with
  | nil => simp [rawReadEquations]
  | cons e E ih =>
    simp only [rawReadEquations, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.flatMap_cons, List.drop_zero, List.map_cons] at *
    simp only [Nat.zero_mul, List.drop_zero, List.singleton_append]
    rw [List.append_assoc]
    simp only [List.cons_append, List.nil_append, rawReadEquation_code]
    congr 1
    rw [← ih]
    apply List.map_congr_left
    intro i hi
    dsimp only [Function.comp_def]
    congr 1
    have hlen : (wordCode e.1 ++ [bitBool e.2]).length = n + 1 := by simp
    have heq : (i+1)*(n+1) = (n+1) + i*(n+1) := by ring
    change (wordCode e.1 ++ ([bitBool e.2] ++
      E.flatMap (fun e => wordCode e.1 ++ [bitBool e.2]))).drop ((i+1)*(n+1)) = _
    rw [← List.append_assoc, heq, ← List.drop_drop]
    have hdrop : ((wordCode e.1 ++ [bitBool e.2]) ++
        E.flatMap (fun e => wordCode e.1 ++ [bitBool e.2])).drop (n+1) =
        E.flatMap (fun e => wordCode e.1 ++ [bitBool e.2]) := by
      rw [← hlen, List.drop_left]
    rw [hdrop]

 theorem rawCounter_correct {n : ℕ} (E : List (Equation n)) :
    rawCounter (unary n ++ equationCode E) = affineCount E := by
  simp only [rawCounter, equationCode, readUnary_prefix, dropHeader_prefix]
  change rawCount n (rawReadEquations n E.length
    (E.flatMap (fun e => wordCode e.1 ++ [bitBool e.2]))) = _
  rw [rawReadEquations_codes, rawCount_equations]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev RawAffine := List (List Bool) × List Bool
abbrev rawAffineEncoding := encPair (encList encBits) encBits

def rawDot (x y : List Bool) : Bool := (x.zipWith Bool.and y).foldl Bool.xor false

def rawUnit (n k : ℕ) : List Bool := (List.range n).map (fun i => decide (i=k))

def rawRow (A : List (List Bool)) (i : ℕ) : List Bool := A[i]?.getD []

def rawColumn (n : ℕ) (A : List (List Bool)) (j : ℕ) : List Bool :=
  (List.range n).map (fun i => (rawRow A i)[j]?.getD false)

def rawPull (n : ℕ) (f : RawAffine) (h : List Bool) : RawEquation :=
  ((List.range n).map (fun j => Bool.xor (h[j]?.getD false)
      (rawDot h (rawColumn n f.1 j))), rawDot h f.2)

def rawFixed (n : ℕ) (f : RawAffine) : List RawEquation :=
  (List.range n).map (fun i =>
    ((rawUnit n i).zipWith Bool.xor (rawRow f.1 i), f.2[i]?.getD false))

def rawCollision (n : ℕ) (f : RawAffine) (G : List (List Bool)) : List RawEquation :=
  G.map (rawPull n f)

@[fun_prop]
theorem rawDot_polytime : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => rawDot p.1 p.2)
    (encPair encBits encBits) encBool := by
  exact bitsFoldlWithInput Bool.xor (bitsZipWith Bool.and) (const false)

@[fun_prop]
theorem rawUnit_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => rawUnit p.1 p.2)
    (encPair encUnary encUnary) encBits := by
  unfold rawUnit
  apply mapToBitsWithInput (range.comp (fst _ _))
  exact unary_beq ((snd _ _)) ((fst _ _).snd')

@[fun_prop]
theorem rawRow_polytime : ComputableTidilyInPolyTime
    (fun p : List (List Bool) × ℕ => rawRow p.1 p.2)
    (encPair (encList encBits) encUnary) encBits := by
  unfold rawRow
  exact optionGetDWithInput (getElem? (fst (encList encBits) encUnary) (snd (encList encBits) encUnary)) (const [])

@[fun_prop]
theorem rawColumn_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List (List Bool)) × ℕ => rawColumn p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary (encList encBits)) encUnary) encBits := by
  unfold rawColumn
  have hlist := range.comp ((fst (encPair encUnary (encList encBits)) encUnary).fst')
  apply mapToBitsWithInput hlist
  have ho := fst (encPair (encPair encUnary (encList encBits)) encUnary) encUnary
  have hi := snd (encPair (encPair encUnary (encList encBits)) encUnary) encUnary
  have hr := rawRow_polytime.comp (ho.fst'.snd'.prod hi)
  simpa only [List.getD_eq_getElem?_getD, Function.comp_def] using bitsGetDWithInput hr ho.snd' false

@[fun_prop]
theorem rawPull_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × RawAffine) × List Bool => rawPull p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary rawAffineEncoding) encBits) rawEquationEncoding := by
  unfold rawPull
  let en := encPair (encPair encUnary rawAffineEncoding) encBits
  have hp := fst (encPair encUnary rawAffineEncoding) encBits
  have hn := hp.fst'
  have hf := hp.snd'
  have hh := snd (encPair encUnary rawAffineEncoding) encBits
  have hright := rawDot_polytime.comp (hh.prod hf.snd')
  have hlist := range.comp hn
  have hleft : ComputableTidilyInPolyTime
      (fun p : (ℕ × RawAffine) × List Bool => (List.range p.1.1).map
        (fun j => Bool.xor (p.2[j]?.getD false) (rawDot p.2 (rawColumn p.1.1 p.1.2.1 j))))
      en encBits := by
    apply mapToBitsWithInput hlist
    have ho := fst en encUnary
    have hj := snd en encUnary
    have hc := rawColumn_polytime.comp ((ho.fst'.fst'.prod ho.fst'.snd'.fst').prod hj)
    have hd := rawDot_polytime.comp (ho.snd'.prod hc)
    have hb := bitsGetDWithInput ho.snd' hj false
    have hx : ComputableTidilyInPolyTime (fun p : Bool × Bool => Bool.xor p.1 p.2)
        (encPair encBool encBool) encBool := of_finite _
    simpa only [Function.comp_def, List.getD_eq_getElem?_getD] using hx.comp (hb.prod hd)
  exact hleft.prod hright

@[fun_prop]
theorem rawFixed_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × RawAffine => rawFixed p.1 p.2)
    (encPair encUnary rawAffineEncoding) (encList rawEquationEncoding) := by
  unfold rawFixed
  let en := encPair encUnary rawAffineEncoding
  have hlist := range.comp (fst encUnary rawAffineEncoding)
  apply mapWithInput (encB := rawEquationEncoding) hlist
  have ho := fst en encUnary
  have hi := snd en encUnary
  have hu := rawUnit_polytime.comp (ho.fst'.prod hi)
  have hr := rawRow_polytime.comp (ho.snd'.fst'.prod hi)
  have hb := bitsGetDWithInput ho.snd'.snd' hi false
  simpa only [Function.comp_def, List.getD_eq_getElem?_getD] using
    ((bitsZipWith Bool.xor).comp (hu.prod hr)).prod hb

set_option maxHeartbeats 1200000 in
theorem rawCollision_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × RawAffine) × List (List Bool) => rawCollision p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary rawAffineEncoding) (encList encBits)) (encList rawEquationEncoding) := by
  unfold rawCollision
  let en := encPair (encPair encUnary rawAffineEncoding) (encList encBits)
  apply mapWithInput (encB := rawEquationEncoding)
    (snd (encPair encUnary rawAffineEncoding) (encList encBits))
  have ho := fst en encBits
  have hh := snd en encBits
  exact rawPull_polytime.comp (ho.fst'.prod hh)

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

@[simp] theorem bitBool_mul (a b : Bit) : bitBool (a*b) = (bitBool a && bitBool b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem bitBool_foldl (L : List Bit) (a : Bit) :
    bitBool (L.foldl (·+·) a) = (L.map bitBool).foldl Bool.xor (bitBool a) := by
  induction L generalizing a with
  | nil => rfl
  | cons b L ih => simp only [List.foldl_cons, List.map_cons, ← bitBool_add, ih]

theorem bitBool_sum (L : List Bit) : bitBool L.sum = (L.map bitBool).foldl Bool.xor false := by
  simpa only [List.sum_eq_foldl, bitBool_zero] using bitBool_foldl L 0

theorem rawDot_words {n : ℕ} (x y : Word n) :
    rawDot (wordCode x) (wordCode y) = bitBool (dot x y) := by
  have he : (wordCode x).zipWith Bool.and (wordCode y) =
      (List.ofFn (fun i : Fin n => x i * y i)).map bitBool := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hi' : i < n := by simpa using hi
      simp [wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters,
        List.getElem_zipWith, ← bitBool_mul, bitBool]
  rw [rawDot, he, ← bitBool_sum, List.sum_ofFn]
  rfl

 theorem rawUnit_word {n k : ℕ} : rawUnit n k = wordCode (unitWord n k) := by
  apply List.ext_getElem
  · simp [rawUnit]
  · intro i hi hj
    simp [rawUnit, wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters,
      unitWord, bitBool]

def rawAffine {n : ℕ} (f : Affine n) : RawAffine :=
  (List.ofFn (fun i : Fin n => wordCode (f.matrix i)), wordCode f.offset)

@[simp] theorem rawRow_matrix {n : ℕ} (f : Affine n) (i : Fin n) :
    rawRow (rawAffine f).1 i.val = wordCode (f.matrix i) := by
  simp [rawRow, rawAffine]

 theorem rawColumn_matrix {n : ℕ} (f : Affine n) (j : Fin n) :
    rawColumn n (rawAffine f).1 j.val = wordCode (fun i => f.matrix i j) := by
  apply List.ext_getElem
  · simp [rawColumn]
  · intro i hi hj
    have hi' : i < n := by simpa [rawColumn] using hi
    simp only [rawColumn, List.getElem_map, List.getElem_range]
    rw [rawRow_matrix f ⟨i, hi'⟩, wordCode_get _ j]
    simp [wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters, bitBool]

 theorem rawPull_equation {n : ℕ} (f : Affine n) (h : Word n) :
    rawPull n (rawAffine f) (wordCode h) = rawEquation (pullZero (difference f) h) := by
  apply Prod.ext
  · apply List.ext_getElem
    · simp [rawPull, rawEquation]
    · intro j hj hj'
      have hjn : j < n := by simpa [rawPull] using hj
      simp only [rawPull, List.getElem_map, List.getElem_range]
      rw [wordCode_get h ⟨j,hjn⟩, rawColumn_matrix f ⟨j,hjn⟩, rawDot_words]
      simp only [Option.getD_some, ← bitBool_add]
      have heq : (pullZero (difference f) h).1 ⟨j,hjn⟩ =
          h ⟨j,hjn⟩ + dot h (fun i => f.matrix i ⟨j,hjn⟩) := by
        simp [pullZero, difference, dot, mul_add, Finset.sum_add_distrib]
      simpa [rawEquation, wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters,
        bitBool] using congrArg bitBool heq.symm
  · simpa [rawPull, rawAffine, rawEquation, pullZero, difference] using rawDot_words h f.offset

 theorem rawFixed_equations {n : ℕ} (f : Affine n) :
    rawFixed n (rawAffine f) = (fixedEquations f).map rawEquation := by
  apply List.ext_getElem
  · simp [rawFixed, fixedEquations]
  · intro i hi hj
    have hin : i < n := by simpa [rawFixed] using hi
    simp only [rawFixed, List.getElem_map, List.getElem_range, fixedEquations, List.getElem_ofFn]
    rw [rawUnit_word, rawRow_matrix f ⟨i,hin⟩, ← wordCode_add]
    have hd : unitWord n i + f.matrix ⟨i,hin⟩ = (difference f).matrix ⟨i,hin⟩ := by
      funext j
      simp [unitWord, difference, Fin.ext_iff, eq_comm]
    rw [hd]
    simp only [rawEquation, rawAffine]
    rw [wordCode_get f.offset ⟨i,hin⟩]
    rfl

 theorem rawCollision_equations {n : ℕ} (f : Affine n) (G : Rows n) :
    rawCollision n (rawAffine f) (G.map wordCode) = (collisionEquations f G).map rawEquation := by
  simp only [rawCollision, collisionEquations, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun h hh => rawPull_equation f h)

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev rawContributionEncoding := encPair (encPair encUnary rawAffineEncoding)
  (encPair (encList encBits) (encList rawEquationEncoding))

def rawContribution (n : ℕ) (f : RawAffine) (G : List (List Bool)) (E : List RawEquation) : ℕ :=
  rawCount n (E ++ rawCollision n f G) - rawCount n (E ++ rawFixed n f)

set_option maxHeartbeats 1200000 in
theorem rawContribution_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × RawAffine) × (List (List Bool) × List RawEquation) =>
      rawContribution p.1.1 p.1.2 p.2.1 p.2.2)
    rawContributionEncoding encNat := by
  unfold rawContribution
  have hnF := fst (encPair encUnary rawAffineEncoding) (encPair (encList encBits) (encList rawEquationEncoding))
  have hGE := snd (encPair encUnary rawAffineEncoding) (encPair (encList encBits) (encList rawEquationEncoding))
  have hn := hnF.fst'
  have hE := hGE.snd'
  have hc := rawCollision_polytime.comp (hnF.prod hGE.fst')
  have hf := rawFixed_polytime.comp hnF
  have hleft := rawCount_polytime.comp (hn.prod (listAppend' hE hc))
  have hright := rawCount_polytime.comp (hn.prod (listAppend' hE hf))
  exact binary_sub.comp (hleft.prod hright)

abbrev rawWitnessEncoding := encPair (encPair encUnary (encList rawAffineEncoding))
  (encPair (encList encBits) (encList rawEquationEncoding))

def rawWitness (n : ℕ) (F : List RawAffine) (G : List (List Bool)) (E : List RawEquation) : ℕ :=
  (F.map (fun f => rawContribution n f G E)).sum

set_option maxHeartbeats 1200000 in
theorem rawWitness_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawAffine) × (List (List Bool) × List RawEquation) =>
      rawWitness p.1.1 p.1.2 p.2.1 p.2.2)
    rawWitnessEncoding encNat := by
  unfold rawWitness
  apply binary_sum.comp
  have hF := (fst (encPair encUnary (encList rawAffineEncoding))
    (encPair (encList encBits) (encList rawEquationEncoding))).snd'
  apply mapWithInput (encB := encNat) hF
  have ho := fst rawWitnessEncoding rawAffineEncoding
  have hf := snd rawWitnessEncoding rawAffineEncoding
  exact rawContribution_polytime.comp ((ho.fst'.fst'.prod hf).prod ho.snd')

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawContribution_equations {n : ℕ} (f : Affine n) (G : Rows n) (E : List (Equation n)) :
    rawContribution n (rawAffine f) (G.map wordCode) (E.map rawEquation) =
      affineCount (E ++ collisionEquations f G) - affineCount (E ++ fixedEquations f) := by
  unfold rawContribution
  rw [rawCollision_equations, rawFixed_equations, ← List.map_append, ← List.map_append,
    rawCount_equations, rawCount_equations]

 theorem rawWitness_equations {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) :
    rawWitness n (F.map rawAffine) (G.map wordCode) (E.map rawEquation) = witnessCount F G E := by
  unfold rawWitness witnessCount
  simp only [List.map_map, Function.comp_def, rawContribution_equations]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev rawSuffixEncoding := encPair (encPair encUnary (encList rawAffineEncoding))
  (encPair (encList encBits) encUnary)
abbrev rawPrefixEncoding := encPair (encPair encUnary (encList rawAffineEncoding))
  (encPair (encList encBits) encBits)

def rawPad (n : ℕ) (w : List Bool) : List Bool :=
  (List.range n).map (fun i => w[i]?.getD false)

theorem rawPad_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool => rawPad p.1 p.2) (encPair encUnary encBits) encBits := by
  unfold rawPad
  apply mapToBitsWithInput (range.comp (fst _ _))
  have ho := fst (encPair encUnary encBits) encUnary
  have hi := snd (encPair encUnary encBits) encUnary
  simpa only [List.getD_eq_getElem?_getD] using bitsGetDWithInput ho.snd' hi false

def rawZeroSuffix (n : ℕ) (F : List RawAffine) (G : List (List Bool)) (j : ℕ) : ℕ :=
  (F.map (fun f => rawContribution n f G ((rawFixed n f).drop j))).sum

def rawZeroPrefix (n : ℕ) (F : List RawAffine) (G : List (List Bool)) (p : List Bool) : ℕ :=
  (F.map (fun f => rawContribution n f G
    ((rawFixed n f).drop p.length ++ [rawPull n f (rawPad n p)]))).sum

def rawTwiceExpectation (n : ℕ) (F : List RawAffine) (G : List (List Bool)) (p : List Bool) : ℕ :=
  (rawWitness n F G [] + 2 * rawZeroPrefix n F G p) - rawZeroSuffix n F G p.length

set_option maxHeartbeats 1600000 in
theorem rawZeroSuffix_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawAffine) × (List (List Bool) × ℕ) =>
      rawZeroSuffix p.1.1 p.1.2 p.2.1 p.2.2) rawSuffixEncoding encNat := by
  unfold rawZeroSuffix
  apply binary_sum.comp
  have hF := (fst (encPair encUnary (encList rawAffineEncoding))
    (encPair (encList encBits) encUnary)).snd'
  apply mapWithInput (encB := encNat) hF
  have ho := fst rawSuffixEncoding rawAffineEncoding
  have hf := snd rawSuffixEncoding rawAffineEncoding
  have hnf := ho.fst'.fst'.prod hf
  have hfixed := rawFixed_polytime.comp hnf
  have hE := listDropWithInput hfixed ho.snd'.snd'
  exact rawContribution_polytime.comp (hnf.prod (ho.snd'.fst'.prod hE))

set_option maxHeartbeats 1600000 in
theorem rawZeroPrefix_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawAffine) × (List (List Bool) × List Bool) =>
      rawZeroPrefix p.1.1 p.1.2 p.2.1 p.2.2) rawPrefixEncoding encNat := by
  unfold rawZeroPrefix
  apply binary_sum.comp
  have hF := (fst (encPair encUnary (encList rawAffineEncoding))
    (encPair (encList encBits) encBits)).snd'
  apply mapWithInput (encB := encNat) hF
  have ho := fst rawPrefixEncoding rawAffineEncoding
  have hf := snd rawPrefixEncoding rawAffineEncoding
  have hnf := ho.fst'.fst'.prod hf
  have hp := ho.snd'.snd'
  have hfixed := rawFixed_polytime.comp hnf
  have htail := listDropWithInput hfixed (length_bits_comp hp)
  have hpad := rawPad_polytime.comp (ho.fst'.fst'.prod hp)
  have hpull := rawPull_polytime.comp (hnf.prod hpad)
  have hsingle := cons' hpull (const [])
  exact rawContribution_polytime.comp (hnf.prod
    (ho.snd'.fst'.prod (listAppend' htail hsingle)))

set_option maxHeartbeats 1600000 in
theorem rawTwiceExpectation_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawAffine) × (List (List Bool) × List Bool) =>
      rawTwiceExpectation p.1.1 p.1.2 p.2.1 p.2.2) rawPrefixEncoding encNat := by
  unfold rawTwiceExpectation
  have hnf := fst (encPair encUnary (encList rawAffineEncoding))
    (encPair (encList encBits) encBits)
  have hgp := snd (encPair encUnary (encList rawAffineEncoding))
    (encPair (encList encBits) encBits)
  have hw := rawWitness_polytime.comp (hnf.prod (hgp.fst'.prod
    (const (encMid := encList rawEquationEncoding) [])))
  have hs := rawZeroSuffix_polytime.comp (hnf.prod (hgp.fst'.prod (length_bits_comp hgp.snd')))
  have ht := binary_mul.comp ((const (encMid := encNat) 2).prod rawZeroPrefix_polytime)
  exact binary_sub.comp ((binary_add.comp (hw.prod ht)).prod hs)

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawPad_prefix {n : ℕ} (p : List Bit) :
    rawPad n (bitCode p) = wordCode (listWord n p) := by
  apply List.ext_getElem
  · simp [rawPad]
  · intro i hi hj
    have hi' : i < n := by simpa [rawPad] using hi
    simp only [rawPad, List.getElem_map, List.getElem_range]
    change ((p.map bitBool)[i]?).getD false =
      (wordCode (listWord n p))[i]'hj
    have he := wordCode_get (listWord n p) ⟨i,hi'⟩
    have hr : (wordCode (listWord n p))[i]'hj = bitBool (p[i]?.getD 0) := by
      have hsome := List.getElem?_eq_getElem hj
      rw [hsome] at he
      exact Option.some.inj he
    rw [hr]
    cases hp : p[i]? with
    | none => simp [List.getElem?_map, hp]
    | some b => simp [List.getElem?_map, hp]

 theorem rawZeroSuffix_equations {n : ℕ} (F : Family n) (G : Rows n) (j : ℕ) :
    rawZeroSuffix n (F.map rawAffine) (G.map wordCode) j = zeroSuffixCount F G j := by
  unfold rawZeroSuffix zeroSuffixCount
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro f hf
  rw [rawFixed_equations, ← List.map_drop, rawContribution_equations]

 theorem rawZeroPrefix_equations {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) :
    rawZeroPrefix n (F.map rawAffine) (G.map wordCode) (bitCode p) = zeroPrefixCount F G p := by
  unfold rawZeroPrefix zeroPrefixCount
  simp only [List.map_map, Function.comp_def, bitCode, List.length_map]
  congr 1
  apply List.map_congr_left
  intro f hf
  change rawContribution n (rawAffine f) (G.map wordCode)
    ((rawFixed n (rawAffine f)).drop p.length ++ [rawPull n (rawAffine f) (rawPad n (bitCode p))]) = _
  rw [rawFixed_equations, ← List.map_drop, rawPad_prefix, rawPull_equation,
    ← List.map_singleton, ← List.map_append, rawContribution_equations]

 theorem witnessCount_le_empty {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) :
    witnessCount F G E ≤ witnessCount F G [] := by
  rw [witnessCount_correct, witnessCount_correct]
  have he : affineSet ([] : List (Equation n)) = Finset.univ := by
    ext x
    simp [affineSet]
  rw [he]
  unfold witnessSum
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

 theorem zeroSuffixCount_le_witness {n : ℕ} (F : Family n) (G : Rows n) (j : ℕ) :
    zeroSuffixCount F G j ≤ witnessCount F G [] := by
  unfold zeroSuffixCount witnessCount
  apply List.sum_le_sum
  intro f hf
  simpa [witnessCount] using witnessCount_le_empty [f] G ((fixedEquations f).drop j)

 theorem rawTwiceExpectation_eq {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) :
    (rawTwiceExpectation n (F.map rawAffine) (G.map wordCode) (bitCode p) : ℤ) =
      twiceExpectation F G p := by
  unfold rawTwiceExpectation
  rw [rawZeroSuffix_equations, rawZeroPrefix_equations]
  have hp : (bitCode p).length = p.length := by simp [bitCode]
  rw [hp]
  have hw : rawWitness n (F.map rawAffine) (G.map wordCode) [] = witnessCount F G [] :=
    rawWitness_equations F G []
  rw [hw, Int.natCast_sub (by have h := zeroSuffixCount_le_witness F G p.length; omega)]
  unfold twiceExpectation
  push_cast
  ring

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawReadRows (n b : ℕ) (w : List Bool) : List (List Bool) :=
  (List.range b).map (fun i => (w.drop (i*n)).take n)

def rawReadAffine (n : ℕ) (w : List Bool) : RawAffine :=
  (rawReadRows n n w, (w.drop (n*n)).take n)

def rawReadFamily (n M : ℕ) (w : List Bool) : List RawAffine :=
  (List.range M).map (fun i => rawReadAffine n (w.drop (i*(n*n+n))))

/-- Return dimension, family, parity rows, and the remaining unparsed suffix. -/
def rawParseFamilyRows (w : List Bool) :
    (ℕ × List RawAffine) × (List (List Bool) × List Bool) :=
  let n := readUnary w
  let w₁ := dropHeader w
  let M := readUnary w₁
  let w₂ := dropHeader w₁
  let F := rawReadFamily n M w₂
  let w₃ := w₂.drop (M*(n*n+n))
  let b := readUnary w₃
  let w₄ := dropHeader w₃
  ((n,F),(rawReadRows n b w₄, w₄.drop (b*n)))

/-- Parse the final length-framed prefix after the family and parity rows. -/
def rawParseExpectation (w : List Bool) :
    (ℕ × List RawAffine) × (List (List Bool) × List Bool) :=
  let p := rawParseFamilyRows w
  (p.1, (p.2.1, (dropHeader p.2.2).take (readUnary p.2.2)))

@[fun_prop]
theorem rawReadRows_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × List Bool => rawReadRows p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encBits) (encList encBits) := by
  unfold rawReadRows
  have hl := range.comp ((fst (encPair encUnary encUnary) encBits).snd')
  apply mapWithInput (encB := encBits) hl
  have ho := fst (encPair (encPair encUnary encUnary) encBits) encUnary
  have hi := snd (encPair (encPair encUnary encUnary) encBits) encUnary
  have hn := ho.fst'.fst'
  exact bitsTakeWithInput (bitsDropWithInput ho.snd' (unary_mul.comp (hi.prod hn))) hn

@[fun_prop]
theorem rawReadAffine_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool => rawReadAffine p.1 p.2)
    (encPair encUnary encBits) rawAffineEncoding := by
  unfold rawReadAffine
  have hn := fst encUnary encBits
  have hw := snd encUnary encBits
  exact (rawReadRows_polytime.comp ((hn.prod hn).prod hw)).prod
    (bitsTakeWithInput (bitsDropWithInput hw (unary_mul.comp (hn.prod hn))) hn)

@[fun_prop]
theorem rawReadFamily_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × List Bool => rawReadFamily p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encBits) (encList rawAffineEncoding) := by
  unfold rawReadFamily
  have hl := range.comp ((fst (encPair encUnary encUnary) encBits).snd')
  apply mapWithInput (encB := rawAffineEncoding) hl
  have ho := fst (encPair (encPair encUnary encUnary) encBits) encUnary
  have hi := snd (encPair (encPair encUnary encUnary) encBits) encUnary
  have hn := ho.fst'.fst'
  have hwidth := unary_add.comp ((unary_mul.comp (hn.prod hn)).prod hn)
  exact rawReadAffine_polytime.comp (hn.prod
    (bitsDropWithInput ho.snd' (unary_mul.comp (hi.prod hwidth))))

@[fun_prop]
theorem rawParseFamilyRows_polytime : ComputableTidilyInPolyTime rawParseFamilyRows
    encBits rawPrefixEncoding := by
  unfold rawParseFamilyRows
  have hn := readUnary_polytime
  have hw₁ := dropHeader_polytime
  have hM := readUnary_polytime.comp hw₁
  have hw₂ := dropHeader_polytime.comp hw₁
  have hF := rawReadFamily_polytime.comp ((hn.prod hM).prod hw₂)
  have hwidth := unary_add.comp ((unary_mul.comp (hn.prod hn)).prod hn)
  have hw₃ := bitsDropWithInput hw₂ (unary_mul.comp (hM.prod hwidth))
  have hb := readUnary_polytime.comp hw₃
  have hw₄ := dropHeader_polytime.comp hw₃
  have hG := rawReadRows_polytime.comp ((hn.prod hb).prod hw₄)
  exact (hn.prod hF).prod (hG.prod (bitsDropWithInput hw₄ (unary_mul.comp (hb.prod hn))))

@[fun_prop]
theorem rawParseExpectation_polytime : ComputableTidilyInPolyTime rawParseExpectation
    encBits rawPrefixEncoding := by
  unfold rawParseExpectation
  have hr := rawParseFamilyRows_polytime
  have ht := hr.snd'.snd'
  exact hr.fst'.prod (hr.snd'.fst'.prod (bitsTakeWithInput
    (dropHeader_polytime.comp ht) (readUnary_polytime.comp ht)))

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem flatMap_length_fixed {α : Type} (xs : List α) (f : α → List Bool) (w : ℕ)
    (hf : ∀ a ∈ xs, (f a).length = w) : (xs.flatMap f).length = xs.length*w := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.flatMap_cons, List.length_append, hf a (by simp),
      ih (fun a ha => hf a (by simp [ha]))]
    simp [Nat.add_mul, Nat.add_comm]

 theorem decode_fixed_blocks {α β : Type} (w : ℕ) (enc : α → List Bool)
    (dec : List Bool → β) (out : α → β)
    (hlen : ∀ a, (enc a).length = w)
    (hread : ∀ a tail, dec (enc a ++ tail) = out a)
    (xs : List α) (tail : List Bool) :
    (List.range xs.length).map (fun i => dec ((xs.flatMap enc ++ tail).drop (i*w))) = xs.map out := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.flatMap_cons, List.append_assoc, Nat.zero_mul, List.drop_zero]
    rw [hread]
    congr 1
    rw [← ih]
    apply List.map_congr_left
    intro i hi
    dsimp only [Function.comp_def]
    have heq : (i+1)*w = w+i*w := by ring
    have hdrop : (enc a ++ (xs.flatMap enc ++ tail)).drop w = xs.flatMap enc ++ tail := by
      rw [← hlen a, List.drop_left]
    rw [heq, ← List.drop_drop, hdrop]

 theorem rawReadRows_codes {n : ℕ} (G : Rows n) (tail : List Bool) :
    rawReadRows n G.length (G.flatMap wordCode ++ tail) = G.map wordCode := by
  apply decode_fixed_blocks n wordCode (List.take n) wordCode wordCode_length
    (fun a tail => ?_) G tail
  exact List.take_left' (wordCode_length a)

 def affineBytes {n : ℕ} (f : Affine n) : List Bool :=
  (List.ofFn (fun i : Fin n => wordCode (f.matrix i))).flatten ++ wordCode f.offset

 theorem matrixBytes_length {n : ℕ} (f : Affine n) :
    (List.ofFn (fun i : Fin n => wordCode (f.matrix i))).flatten.length = n*n := by
  rw [List.flatten_eq_flatMap]
  have hh := flatMap_length_fixed (List.ofFn (fun i : Fin n => wordCode (f.matrix i))) id n
    (by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact wordCode_length _)
  simpa only [List.length_ofFn] using hh

 theorem affineBytes_length {n : ℕ} (f : Affine n) : (affineBytes f).length = n*n+n := by
  simp only [affineBytes, List.length_append, matrixBytes_length, wordCode_length]

 theorem rawReadAffine_code {n : ℕ} (f : Affine n) (tail : List Bool) :
    rawReadAffine n (affineBytes f ++ tail) = rawAffine f := by
  apply Prod.ext
  · change rawReadRows n n _ = _
    let G : Rows n := List.ofFn (fun i : Fin n => f.matrix i)
    have hG : G.length = n := by simp [G]
    have hm : G.flatMap wordCode = (List.ofFn (fun i : Fin n => wordCode (f.matrix i))).flatten := by
      simp [G, List.flatMap, List.map_ofFn, Function.comp_def]
    have hh := rawReadRows_codes G (wordCode f.offset ++ tail)
    simpa only [hG, hm, G, affineBytes, rawAffine, List.append_assoc, List.map_ofFn, Function.comp_def] using hh
  · change ((affineBytes f ++ tail).drop (n*n)).take n = wordCode f.offset
    unfold affineBytes
    rw [List.append_assoc, ← matrixBytes_length f, List.drop_left]
    exact List.take_left' (wordCode_length f.offset)

 theorem rawReadFamily_codes {n : ℕ} (F : Family n) (tail : List Bool) :
    rawReadFamily n F.length (F.flatMap affineBytes ++ tail) = F.map rawAffine := by
  exact decode_fixed_blocks (n*n+n) affineBytes (rawReadAffine n) rawAffine
    affineBytes_length rawReadAffine_code F tail

 theorem rawParseFamilyRows_correct {n : ℕ} (F : Family n) (G : Rows n) (tail : List Bool) :
    rawParseFamilyRows (familyRowsInput F G ++ tail) =
      ((n,F.map rawAffine),(G.map wordCode,tail)) := by
  have hF : (F.flatMap affineBytes).length = F.length*(n*n+n) :=
    flatMap_length_fixed F affineBytes _ (fun a ha => affineBytes_length a)
  have hG : (G.flatMap wordCode).length = G.length*n :=
    flatMap_length_fixed G wordCode _ (fun a ha => wordCode_length a)
  change rawParseFamilyRows (((unary n ++ (unary F.length ++ F.flatMap affineBytes)) ++
      (unary G.length ++ G.flatMap wordCode)) ++ tail) = _
  simp only [rawParseFamilyRows, List.append_assoc, readUnary_prefix, dropHeader_prefix]
  rw [rawReadFamily_codes]
  rw [← hF, List.drop_left]
  simp only [readUnary_prefix, dropHeader_prefix]
  rw [rawReadRows_codes, ← hG, List.drop_left]

 theorem rawParseExpectation_correct {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) :
    rawParseExpectation (expectationInput F G p) =
      ((n,F.map rawAffine),(G.map wordCode,bitCode p)) := by
  unfold rawParseExpectation expectationInput
  rw [rawParseFamilyRows_correct]
  simp only [frame, dropHeader_prefix, readUnary_prefix, List.take_length]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev RawRowData := (ℕ × List RawAffine) × List (List Bool)
abbrev rawRowEncoding := encPair (encPair encUnary (encList rawAffineEncoding)) (encList encBits)

def rawGreedyStep (D : RawRowData) (p : List Bool) : List Bool :=
  let a := rawTwiceExpectation D.1.1 D.1.2 D.2 (p ++ [false])
  let b := rawTwiceExpectation D.1.1 D.1.2 D.2 (p ++ [true])
  p ++ [if a ≤ b then false else true]

def rawChooseRow (D : RawRowData) : List Bool := (rawGreedyStep D)^[D.1.1] []

set_option maxHeartbeats 1600000 in
theorem rawGreedyStep_polytime : ComputableTidilyInPolyTime
    (fun p : RawRowData × List Bool => rawGreedyStep p.1 p.2)
    (encPair rawRowEncoding encBits) encBits := by
  unfold rawGreedyStep
  have hd := fst rawRowEncoding encBits
  have hp := snd rawRowEncoding encBits
  have hfalse := bitsAppend hp (const [false])
  have htrue := bitsAppend hp (const [true])
  have ha := rawTwiceExpectation_polytime.comp (hd.fst'.prod (hd.snd'.prod hfalse))
  have hb := rawTwiceExpectation_polytime.comp (hd.fst'.prod (hd.snd'.prod htrue))
  have hc := binary_le.comp (ha.prod hb)
  have hbit := hc.cond (const (encMid := encBool) false) (const (encMid := encBool) true)
  have hs := bitsCons hbit (const [])
  simpa only [Function.comp_def, decide_eq_true_eq] using bitsAppend hp hs

 theorem rawChooseRow_polytime : ComputableTidilyInPolyTime rawChooseRow rawRowEncoding encBits := by
  unfold rawChooseRow
  apply iterateWithInput_of_bounded_growth ((fst _ _).fst') (const []) rawGreedyStep_polytime
    (growth := fun _ => 1)
  refine ⟨.const 1, ?_⟩
  intro D p
  simp [rawGreedyStep]

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawFrame (w : List Bool) : List Bool := List.replicate w.length true ++ false :: w

def rawNaturalCode (n : ℕ) : List Bool := false :: rawFrame n.bits.reverse

def rawEvaluateInput (w : List Bool) : ℕ :=
  let D := rawParseExpectation w
  rawTwiceExpectation D.1.1 D.1.2 D.2.1 D.2.2

def rawBuildRowInput (w : List Bool) : List Bool :=
  let D := rawParseFamilyRows w
  rawChooseRow (D.1, D.2.1)

 theorem rawFrame_polytime : ComputableTidilyInPolyTime rawFrame encBits encBits := by
  exact bitsAppend ((bitsReplicate true).comp length_bits) (bitsCons (const false) id')

 theorem rawNaturalCode_polytime : ComputableTidilyInPolyTime rawNaturalCode encNat encBits := by
  exact bitsCons (const false) (rawFrame_polytime.comp (bitsReverse.comp (encode encNat)))

set_option maxHeartbeats 1600000 in
theorem rawEvaluateInput_polytime : ComputableTidilyInPolyTime
    (fun w => rawNaturalCode (rawEvaluateInput w)) encBits encBits := by
  exact rawNaturalCode_polytime.comp (rawTwiceExpectation_polytime.comp rawParseExpectation_polytime)

 theorem rawBuildRowInput_polytime : ComputableTidilyInPolyTime rawBuildRowInput encBits encBits := by
  exact rawChooseRow_polytime.comp
    (rawParseFamilyRows_polytime.fst'.prod rawParseFamilyRows_polytime.snd'.fst')

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawGreedyStep_correct {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) :
    rawGreedyStep ((n,F.map rawAffine),G.map wordCode) (bitCode p) =
      bitCode (p ++ [if twiceExpectation F G (p++[0]) ≤ twiceExpectation F G (p++[1]) then 0 else 1]) := by
  have h0 : bitCode p ++ [false] = bitCode (p++[0]) := by simp [bitCode]
  have h1 : bitCode p ++ [true] = bitCode (p++[1]) := by simp [bitCode]
  have hc : rawTwiceExpectation n (F.map rawAffine) (G.map wordCode) (bitCode (p++[0])) ≤
        rawTwiceExpectation n (F.map rawAffine) (G.map wordCode) (bitCode (p++[1])) ↔
      twiceExpectation F G (p++[0]) ≤ twiceExpectation F G (p++[1]) := by
    rw [← rawTwiceExpectation_eq F G (p++[0]), ← rawTwiceExpectation_eq F G (p++[1])]
    omega
  dsimp only [rawGreedyStep]
  rw [h0,h1]
  simp only [hc]
  split_ifs <;> simp [bitCode]

 theorem rawGreedy_iterate {n : ℕ} (F : Family n) (G : Rows n) (k : ℕ) (p : List Bit) :
    (rawGreedyStep ((n,F.map rawAffine),G.map wordCode))^[k] (bitCode p) =
      bitCode (chooseRowPrefix F G k p) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, rawGreedyStep_correct, ih]
    rfl

 theorem greedyPrefix_length {n : ℕ} (F : Family n) (G : Rows n) (k : ℕ) (p : List Bit) :
    (chooseRowPrefix F G k p).length = p.length+k := by
  induction k generalizing p with
  | zero => simp [chooseRowPrefix]
  | succ k ih =>
    dsimp only [chooseRowPrefix]
    rw [ih]
    simp
    omega

 theorem rawChooseRow_correct {n : ℕ} (F : Family n) (G : Rows n) :
    rawChooseRow ((n,F.map rawAffine),G.map wordCode) = wordCode (chooseRow F G) := by
  have hh := rawGreedy_iterate F G n []
  change _ = bitCode (wordList (listWord n (chooseRowPrefix F G n [])))
  rw [wordList_listWord _ (by simpa using greedyPrefix_length F G n [])]
  exact hh

end EditGV897.Main

namespace EditGV897.Main

 theorem familyRowsInput_length {n : ℕ} (F : Family n) (G : Rows n) :
    (familyRowsInput F G).length =
      n+F.length+G.length+3+F.length*(n*n+n)+G.length*n := by
  have hF := flatMap_length_fixed F affineBytes (n*n+n) (fun a ha => affineBytes_length a)
  have hG := flatMap_length_fixed G wordCode n (fun a ha => wordCode_length a)
  change ((unary n ++ (unary F.length ++ F.flatMap affineBytes)) ++
    (unary G.length ++ G.flatMap wordCode)).length = _
  simp only [List.length_append, unary, List.length_replicate, List.length_singleton, hF, hG]
  omega

 theorem familyRowsInput_length_bound {n : ℕ} (F : Family n) (G : Rows n) (hG : G.length ≤ n) :
    (familyRowsInput F G).length+1 ≤ 16*(n+F.length+1)^3 := by
  rw [familyRowsInput_length]
  have hGn : G.length*n ≤ n*n := Nat.mul_le_mul_right _ hG
  nlinarith [Nat.zero_le (F.length^3), Nat.zero_le (n^3), Nat.zero_le (n*F.length^2)]

 theorem expectationInput_length_bound {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit)
    (hG : G.length ≤ n) (hp : p.length ≤ n) :
    (expectationInput F G p).length+1 ≤ 16*(n+F.length+1)^3 := by
  have hGn : G.length*n ≤ n*n := Nat.mul_le_mul_right _ hG
  have hlen : (expectationInput F G p).length =
      (familyRowsInput F G).length + 2*p.length+1 := by
    simp [expectationInput, frame, unary, bitCode]
    omega
  rw [hlen, familyRowsInput_length]
  nlinarith [Nat.zero_le (F.length^3), Nat.zero_le (n^3), Nat.zero_le (n*F.length^2)]

 theorem rawNaturalCode_eq (m : ℕ) : EditGV897.Runtime.rawNaturalCode m = integerCode (m : ℤ) := by
  simp [EditGV897.Runtime.rawNaturalCode, EditGV897.Runtime.rawFrame, integerCode, frame, unary, binary]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawEvaluateInput_correct {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) :
    rawNaturalCode (rawEvaluateInput (expectationInput F G p)) =
      integerCode (twiceExpectation F G p) := by
  rw [rawNaturalCode_eq]
  congr 1
  dsimp only [rawEvaluateInput]
  rw [rawParseExpectation_correct]
  exact rawTwiceExpectation_eq F G p

 theorem rawBuildRowInput_correct {n : ℕ} (F : Family n) (G : Rows n) :
    rawBuildRowInput (familyRowsInput F G) = wordCode (chooseRow F G) := by
  have hp := rawParseFamilyRows_correct F G []
  simp only [List.append_nil] at hp
  dsimp only [rawBuildRowInput]
  rw [hp]
  exact rawChooseRow_correct F G

 theorem Runs.cubic_input_bound {P : Program} {input output : List Bool} {c d s : ℕ}
    (hr : Runs P input output (polyBudget c d input.length))
    (hlen : input.length+1 ≤ 16*(s+1)^3) :
    Runs P input output (polyBudget (c*16^d) (3*d) s) := by
  apply hr.mono
  unfold polyBudget
  calc
    c*(input.length+1)^d ≤ c*(16*(s+1)^3)^d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)
    _ = c*16^d*(s+1)^(3*d) := by rw [mul_pow, ← pow_mul]; ring

 theorem expectation_runtime_assembly :
    ∃ (evaluator rowBuilder : Program) (A d : ℕ), 0 < A ∧
      ∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length ≤ n →
        (∀ p : List Bit, p.length ≤ n →
          Runs evaluator (expectationInput F G p) (integerCode (twiceExpectation F G p))
            (polyBudget A d (n + F.length))) ∧
        Runs rowBuilder (familyRowsInput F G) (wordCode (chooseRow F G))
          (polyBudget A d (n + F.length)) := by
  obtain ⟨evaluator, ce, de, he, hev⟩ := program_of_tidy_polytime _ _ _ rawEvaluateInput_polytime
  obtain ⟨rowBuilder, cr, dr, hr, hrow⟩ := program_of_tidy_polytime _ _ _ rawBuildRowInput_polytime
  let Ae := ce*16^de
  let Ar := cr*16^dr
  have hAe : 0 < Ae := Nat.mul_pos he (by positivity)
  have hAr : 0 < Ar := Nat.mul_pos hr (by positivity)
  refine ⟨evaluator,rowBuilder,Ae+Ar,3*de+3*dr,by omega,?_⟩
  intro n t F G ht hF hG
  have heval (p : List Bit) (hp : p.length ≤ n) :
      Runs evaluator (expectationInput F G p) (integerCode (twiceExpectation F G p))
        (polyBudget Ae (3*de) (n+F.length)) := by
    have h := (hev (expectationInput F G p)).1
    simp only [Turing.MultiTapeTM.encBits_apply, rawEvaluateInput_correct] at h
    exact h.cubic_input_bound (expectationInput_length_bound F G p hG hp)
  have hrow' : Runs rowBuilder (familyRowsInput F G) (wordCode (chooseRow F G))
      (polyBudget Ar (3*dr) (n+F.length)) := by
    have h := (hrow (familyRowsInput F G)).1
    simp only [Turing.MultiTapeTM.encBits_apply, rawBuildRowInput_correct] at h
    exact h.cubic_input_bound (familyRowsInput_length_bound F G hG)
  have hb (s a c b e : ℕ) (ha : a ≤ Ae+Ar) (hc : c ≤ 3*de+3*dr) :
      polyBudget a c s ≤ polyBudget (Ae+Ar) (3*de+3*dr) s := by
    exact Nat.mul_le_mul ha (Nat.pow_le_pow_right (by omega) hc)
  exact ⟨fun p hp => (heval p hp).mono (hb _ _ _ 0 0 (by omega) (by omega)),
    hrow'.mono (hb _ _ _ 0 0 (by omega) (by omega))⟩

end EditGV897.Main
open EditGV897.Main
theorem solution :
    ∃ (evaluator rowBuilder : Program) (A d : ℕ), 0 < A ∧
      ∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length ≤ n →
        (∀ p : List Bit, p.length ≤ n →
          Runs evaluator (expectationInput F G p) (integerCode (twiceExpectation F G p))
            (polyBudget A d (n + F.length))) ∧
        Runs rowBuilder (familyRowsInput F G) (wordCode (chooseRow F G))
          (polyBudget A d (n + F.length)) := EditGV897.Main.expectation_runtime_assembly