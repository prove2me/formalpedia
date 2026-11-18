-- Prove2me | solution 1 for EditGV897.Main.binary_program_realization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:17.736694+00:00
-- url     : https://prove2.me/submissions/3d2bbf69-af82-4555-9887-c87990b18a88

import Definitions.Def_EditGV897_Main_Machine
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain

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
open EditGV897.Main
theorem solution {α β : Type} (f : α → β)
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f encIn encOut) :
    ∃ (P : Program) (A d : ℕ), 0 < A ∧ ∀ a : α,
      Runs P (encIn a) (encOut (f a)) (polyBudget A d (encIn a).length) ∧
      (encOut (f a)).length ≤ polyBudget A d (encIn a).length := EditGV897.Main.program_of_polytime f encIn encOut hf