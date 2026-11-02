-- Prove2me | solution 2 for CookPvsNP.CanonicalBlockParser.success_strict_progress
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:35:51.355278+00:00
-- url     : https://prove2.me/submissions/fc4edbdc-fdbb-4c45-ac33-c6191288ee08

import Definitions.Def_CookPvsNP_CanonicalBlockParser
import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding

open CookPvsNP ProjSchedTW.Complexity

namespace CanonicalProgressLocal

/-- Three stacks hold unconsumed input, reversed digits, and status markers. -/
private def store (input acc status : List BSym) : Fin 3 → List BSym :=
  fun k ↦ if k = 0 then input else if k = 1 then acc else status

private def digitSym (b : Bool) : BSym := if b then .one else .zero

private def isDigit (o : Option BSym) : Bool :=
  match o with
  | some .zero | some .one => true
  | _ => false

private def digitTest (h : Fin 3 → Option BSym) : Bool := isDigit (h 0)
private def separatorTest (h : Fin 3 → Option BSym) : Bool := h 0 == some BSym.sep

private def readAct (h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then
    match h 0 with
    | some .zero => .push .zero
    | some .one => .push .one
    | _ => .keep
  else .keep

private def acceptAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 then .pop else if k = 2 then .push .one else .keep

private def rejectAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .zero else .keep

/-- A finite program that reads the first 0/1 block, consumes its separator
    on success, and pushes one status marker: one for a separator, zero for a
    missing separator or illegal next symbol. -/
private def parseBlockProg : StackProg (Fin 3) BSym :=
  .seq (.loop digitTest (.act readAct))
    (.branch separatorTest (.act acceptAct) (.act rejectAct))

private theorem readAct_step (b : Bool) (rest acc status : List BSym) :
    StackProg.applyAct readAct (store (digitSym b :: rest) acc status) =
      store rest (digitSym b :: acc) status := by
  funext k
  fin_cases k <;> cases b <;>
    simp [StackProg.applyAct, readAct, store, digitSym, StackAct.apply]

private theorem acceptAct_step (tail acc status : List BSym) :
    StackProg.applyAct acceptAct (store (BSym.sep :: tail) acc status) =
      store tail acc (BSym.one :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, acceptAct, store, StackAct.apply]

private theorem rejectAct_step (rest acc status : List BSym) :
    StackProg.applyAct rejectAct (store rest acc status) =
      store rest acc (BSym.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, rejectAct, store, StackAct.apply]

private theorem scan_exec (digits : List Bool) (stop acc status : List BSym)
    (hstop : isDigit stop.head? = false) :
    (StackProg.loop digitTest (.act readAct)).Exec
      (store (digits.map digitSym ++ stop) acc status)
      (store stop ((digits.map digitSym).reverse ++ acc) status)
      (3 * digits.length + 1) := by
  induction digits generalizing acc with
  | nil =>
    apply StackProg.Exec.loopFalse
    simpa [digitTest, store] using hstop
  | cons b digits ih =>
    have htest : digitTest (fun k ↦ (store (digitSym b ::
        (digits.map digitSym ++ stop)) acc status k).head?) = true := by
      cases b <;> rfl
    have hact : (StackProg.act readAct).Exec
        (store (digitSym b :: (digits.map digitSym ++ stop)) acc status)
        (store (digits.map digitSym ++ stop) (digitSym b :: acc) status) 1 := by
      rw [← readAct_step]
      exact StackProg.Exec.act _ _
    have hloop := StackProg.Exec.loopTrue htest hact (ih (digitSym b :: acc))
    simpa [List.reverse_cons, List.append_assoc, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop

/-- A terminated block is consumed and accepted, with exact cost 3d+4. -/
private theorem parseBlockProg_success (digits : List Bool) (tail acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) acc status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits (BSym.sep :: tail) acc status (by rfl)
  have hact : (StackProg.act acceptAct).Exec
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status)) 1 := by
    rw [← acceptAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status k).head?) = true := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status)) 2 :=
    StackProg.Exec.branchTrue ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega

/-- A minus sign in place of the separator is rejected and left unconsumed. -/
private theorem parseBlockProg_reject_minus (digits : List Bool) (tail acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) acc status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits (BSym.minus :: tail) acc status (by rfl)
  have hact : (StackProg.act rejectAct).Exec
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 1 := by
    rw [← rejectAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status k).head?) = false := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega

/-- End of input in place of the separator is rejected. -/
private theorem parseBlockProg_reject_eof (digits : List Bool) (acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym) acc status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits [] acc status (by rfl)
  have hact : (StackProg.act rejectAct).Exec
      (store [] ((digits.map digitSym).reverse ++ acc) status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 1 := by
    rw [← rejectAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store [] ((digits.map digitSym).reverse ++ acc) status k).head?) = false := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store [] ((digits.map digitSym).reverse ++ acc) status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega


/-- A terminated block is canonical when it is empty or has most significant
    digit one; status zero from the first stage is always rejected. -/
private def canonicalTest (h : Fin 3 → Option BSym) : Bool :=
  (h 2 == some BSym.one) &&
    match h 1 with
    | none | some .one => true
    | _ => false

private def markTrueAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .one else .keep

private def markFalseAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .zero else .keep

/-- The delimiter parser followed by a finite-control canonicality check.
    The top status marker is one exactly on a terminated block that is empty
    or ends in one; the previous delimiter status is kept just below it. -/
private def parseCanonicalBlockProg : StackProg (Fin 3) BSym :=
  .seq parseBlockProg (.branch canonicalTest (.act markTrueAct) (.act markFalseAct))

private theorem markTrue_step (input acc status : List BSym) :
    StackProg.applyAct markTrueAct (store input acc status) =
      store input acc (BSym.one :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, markTrueAct, store, StackAct.apply]

private theorem markFalse_step (input acc status : List BSym) :
    StackProg.applyAct markFalseAct (store input acc status) =
      store input acc (BSym.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, markFalseAct, store, StackAct.apply]

/-- Empty blocks and nonempty blocks ending in one are accepted and leave
    their reversed digits available for decoding. -/
private theorem parseCanonicalBlockProg_accept (digits : List Bool) (tail status : List BSym)
    (hcanon : digits = [] ∨ ∃ pre, digits = pre ++ [true]) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_success digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store tail (digits.map digitSym).reverse (BSym.one :: status) k).head?) = true := by
    rcases hcanon with rfl | ⟨pre, rfl⟩
    · rfl
    · simp [canonicalTest, store, List.map_append, List.reverse_append, digitSym]
  have ha : (StackProg.act markTrueAct).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status)) 1 := by
    simpa only [markTrue_step] using
      (StackProg.Exec.act markTrueAct (store tail (digits.map digitSym).reverse (BSym.one :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status)) 2 :=
    StackProg.Exec.branchTrue ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega

/-- A nonempty block with most significant digit zero is rejected. -/
private theorem parseCanonicalBlockProg_reject_high_zero (pre : List Bool) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store ((pre ++ [false]).map digitSym ++ BSym.sep :: tail) [] status)
      (store tail ((pre ++ [false]).map digitSym).reverse (BSym.zero :: BSym.one :: status))
      (3 * (pre ++ [false]).length + 7) := by
  let digits := pre ++ [false]
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_success digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store tail (digits.map digitSym).reverse (BSym.one :: status) k).head?) = false := by
    simp [digits, canonicalTest, store, List.map_append, List.reverse_append, digitSym]
  have ha : (StackProg.act markFalseAct).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.zero :: BSym.one :: status)) 1 := by
    rw [← markFalse_step]
    exact StackProg.Exec.act _ _
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.zero :: BSym.one :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg, digits] <;> omega


/-- A minus sign where the delimiter is required remains rejected by the full
    two-stage parser, regardless of the scanned digit sequence. -/
private theorem parseCanonicalBlockProg_reject_minus (digits : List Bool) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) [] status)
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) [] status)
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_reject_minus digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status) k).head?) = false := by
    simp [canonicalTest, store]
  have ha : (StackProg.act markFalseAct).Exec
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 1 := by
    simpa only [markFalse_step] using
      (StackProg.Exec.act markFalseAct
        (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega

/-- A missing separator at end of input remains rejected by both stages. -/
private theorem parseCanonicalBlockProg_reject_eof (digits : List Bool) (status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym) [] status)
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym) [] status)
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_reject_eof digits [] status
  have ht : canonicalTest (fun k ↦
      (store [] (digits.map digitSym).reverse (BSym.zero :: status) k).head?) = false := by
    simp [canonicalTest, store]
  have ha : (StackProg.act markFalseAct).Exec
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 1 := by
    simpa only [markFalse_step] using
      (StackProg.Exec.act markFalseAct (store [] (digits.map digitSym).reverse (BSym.zero :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega


/-- Every Boolean block is empty, ends in one, or ends in zero. -/
private theorem digit_end_cases (digits : List Bool) :
    digits = [] ∨ (∃ pre, digits = pre ++ [true]) ∨ ∃ pre, digits = pre ++ [false] := by
  cases hr : digits.reverse with
  | nil =>
    left
    have h := congrArg List.reverse hr
    simpa using h
  | cons b pre =>
    have h : digits = pre.reverse ++ [b] := by
      have h' := congrArg List.reverse hr
      simpa using h'
    cases b with
    | false => exact Or.inr (Or.inr ⟨pre.reverse, h⟩)
    | true => exact Or.inr (Or.inl ⟨pre.reverse, h⟩)

/-- Every alphabet string decomposes into its maximal 0/1 prefix followed by
    a separator, a minus sign, or end of input. -/
private theorem split_digit_prefix (input : List BSym) :
    ∃ digits : List Bool, ∃ stop : List BSym,
      input = digits.map digitSym ++ stop ∧
        (stop = [] ∨ (∃ tail, stop = BSym.sep :: tail) ∨ ∃ tail, stop = BSym.minus :: tail) := by
  induction input with
  | nil => exact ⟨[], [], rfl, Or.inl rfl⟩
  | cons a input ih =>
    cases a with
    | zero =>
      obtain ⟨digits, stop, heq, hstop⟩ := ih
      refine ⟨false :: digits, stop, ?_, hstop⟩
      simp [digitSym, heq]
    | one =>
      obtain ⟨digits, stop, heq, hstop⟩ := ih
      refine ⟨true :: digits, stop, ?_, hstop⟩
      simp [digitSym, heq]
    | minus => exact ⟨[], BSym.minus :: input, by simp, Or.inr (Or.inr ⟨input, rfl⟩)⟩
    | sep => exact ⟨[], BSym.sep :: input, by simp, Or.inr (Or.inl ⟨input, rfl⟩)⟩

/-- The concrete canonical-block parser terminates on every input in linear
    stack-program time, including malformed input and end of input. -/
private theorem parseCanonicalBlockProg_total (input status : List BSym) :
    ∃ out steps, parseCanonicalBlockProg.Exec (store input [] status) out steps ∧
      steps ≤ 3 * input.length + 7 := by
  obtain ⟨digits, stop, hw, hstop⟩ := split_digit_prefix input
  subst input
  have hbound : 3 * digits.length + 7 ≤ 3 * (digits.map digitSym ++ stop).length + 7 := by
    simp only [List.length_append, List.length_map]
    omega
  rcases hstop with hempty | ⟨tail, hsep⟩ | ⟨tail, hminus⟩
  · subst stop
    refine ⟨store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status),
      3 * digits.length + 7, ?_, hbound⟩
    simpa using parseCanonicalBlockProg_reject_eof digits status
  · subst stop
    rcases digit_end_cases digits with hempty | ⟨pre, htrue⟩ | ⟨pre, hfalse⟩
    · refine ⟨store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status),
        3 * digits.length + 7, ?_, hbound⟩
      exact parseCanonicalBlockProg_accept digits tail status (Or.inl hempty)
    · refine ⟨store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status),
        3 * digits.length + 7, ?_, hbound⟩
      exact parseCanonicalBlockProg_accept digits tail status (Or.inr ⟨pre, htrue⟩)
    · subst digits
      refine ⟨store tail ((pre ++ [false]).map digitSym).reverse (BSym.zero :: BSym.one :: status),
        3 * (pre ++ [false]).length + 7, ?_, hbound⟩
      exact parseCanonicalBlockProg_reject_high_zero pre tail status
  · subst stop
    refine ⟨store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status),
      3 * digits.length + 7, ?_, hbound⟩
    exact parseCanonicalBlockProg_reject_minus digits tail status

end CanonicalProgressLocal

namespace CanonicalProgressLocal

private theorem exec_det {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∀ {u : K → List A} {m : ℕ}, p.Exec s u m → t = u := by
  induction h with
  | act f s =>
      intro u m h2
      cases h2
      rfl
  | seq hab hbc ihab ihbc =>
      intro u m h2
      cases h2 with
      | seq hab' hbc' =>
          have e : _ = _ := ihab hab'
          rw [← e] at hbc'
          exact ihbc hbc'
  | branchTrue ht hb ih =>
      intro u m h2
      cases h2 with
      | branchTrue _ hb' => exact ih hb'
      | branchFalse hf _ =>
          rw [ht] at hf
          cases hf
  | branchFalse ht hb ih =>
      intro u m h2
      cases h2 with
      | branchFalse _ hb' => exact ih hb'
      | branchTrue hf _ =>
          rw [ht] at hf
          cases hf
  | loopFalse ht =>
      intro u m h2
      cases h2 with
      | loopFalse _ => rfl
      | loopTrue ht' _ _ =>
          rw [ht] at ht'
          cases ht'
  | loopTrue ht hb hrest ihab ihrest =>
      intro u m h2
      cases h2 with
      | loopFalse ht' =>
          rw [ht] at ht'
          cases ht'
      | loopTrue _ hb' hrest' =>
          have e : _ = _ := ihab hb'
          rw [← e] at hrest'
          exact ihrest hrest'




private theorem classified_progress (input status : List BSym) :
    ∃ rest digits outstatus steps,
      parseCanonicalBlockProg.Exec (store input [] status) (store rest digits outstatus) steps ∧
      (rest.length < input.length ∨ outstatus.head? ≠ some .one) := by
  obtain ⟨digits, stop, hw, hstop⟩ := split_digit_prefix input
  subst input
  rcases hstop with hempty | ⟨tail, hsep⟩ | ⟨tail, hminus⟩
  · subst stop
    refine ⟨[], (digits.map digitSym).reverse, .zero :: .zero :: status, 3*digits.length+7, ?_, Or.inr (by simp)⟩
    simpa using parseCanonicalBlockProg_reject_eof digits status
  · subst stop
    have hshort : tail.length < (digits.map digitSym ++ .sep :: tail).length := by
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    rcases digit_end_cases digits with hempty | ⟨pre, htrue⟩ | ⟨pre, hfalse⟩
    · exact ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status, 3*digits.length+7,
        parseCanonicalBlockProg_accept digits tail status (Or.inl hempty), Or.inl hshort⟩
    · exact ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status, 3*digits.length+7,
        parseCanonicalBlockProg_accept digits tail status (Or.inr ⟨pre, htrue⟩), Or.inl hshort⟩
    · subst digits
      exact ⟨tail, ((pre ++ [false]).map digitSym).reverse, .zero :: .one :: status,
        3*(pre ++ [false]).length+7, parseCanonicalBlockProg_reject_high_zero pre tail status, Or.inl hshort⟩
  · subst stop
    exact ⟨.minus :: tail, (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, parseCanonicalBlockProg_reject_minus digits tail status, Or.inr (by simp)⟩

end CanonicalProgressLocal

/-- A successful canonical block parse always consumes at least one symbol. -/
theorem solution (input status rest digits markerTail : List BSym) (steps : ℕ)
    (h : CookPvsNP.CanonicalBlockParser.parseCanonicalBlockProg.Exec
      (CookPvsNP.CanonicalBlockParser.store input [] status)
      (CookPvsNP.CanonicalBlockParser.store rest digits (.one :: markerTail)) steps) :
    rest.length < input.length := by
  have hl : CanonicalProgressLocal.parseCanonicalBlockProg.Exec
      (CanonicalProgressLocal.store input [] status)
      (CanonicalProgressLocal.store rest digits (.one :: markerTail)) steps := h
  obtain ⟨rest', digits', outstatus, otherSteps, hrun, hclass⟩ :=
    CanonicalProgressLocal.classified_progress input status
  have heq := CanonicalProgressLocal.exec_det hl hrun
  have hrest : rest = rest' := by
    simpa [CanonicalProgressLocal.store] using congrFun heq (0 : Fin 3)
  have hstatus : .one :: markerTail = outstatus := by
    simpa [CanonicalProgressLocal.store] using congrFun heq (2 : Fin 3)
  rcases hclass with hshort | hbad
  · simpa only [hrest] using hshort
  · rw [← hstatus] at hbad
    simp at hbad
