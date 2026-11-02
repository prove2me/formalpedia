-- Prove2me | solution 1 for CookPvsNP.CanonicalBlockParser.execution_and_bounds
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:37:03.648488+00:00
-- url     : https://prove2.me/submissions/bfafa5fb-bbdc-4edb-9ff9-f296838c249f

import Mathlib
import Definitions.Def_CookPvsNP_CanonicalBlockParser

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity



namespace TensorCanonicalDigits

/-- Interpret little-endian Boolean digits as a natural number. -/
def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (bitsValue bs)

/-- Every bit list ending in one is the canonical bit representation of its
    computed value. Thus checking the most significant bit suffices for
    canonicality once a nonempty binary block has been scanned. -/
theorem bitsValue_bits_append_true (pre : List Bool) :
    (bitsValue (pre ++ [true])).bits = pre ++ [true] := by
  induction pre with
  | nil => simp [bitsValue]
  | cons b bs ih =>
    have hne : bitsValue (bs ++ [true]) ≠ 0 := by
      intro hz
      rw [hz, Nat.zero_bits] at ih
      have hcons : bs ++ [true] ≠ [] := by simp
      exact hcons ih.symm
    have hcanonical : bitsValue (bs ++ [true]) = 0 → b = true := by
      intro hz
      exact (hne hz).elim
    simpa [bitsValue, ih] using Nat.bits_append_bit (bitsValue (bs ++ [true])) b hcanonical

/-- Zero is represented by the empty block, and all other canonical bit lists
    end in one. -/
theorem nat_bits_canonical (n : ℕ) : n.bits = [] ∨ ∃ pre, n.bits = pre ++ [true] := by
  induction n using Nat.binaryRecFromOne with
  | zero => exact Or.inl (by simp)
  | one => exact Or.inr ⟨[], by simp⟩
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b (fun hz ↦ (hn hz).elim)]
    rcases ih with hempty | ⟨pre, hprefix⟩
    · have hn0 : n = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp [Nat.testBit_eq_inth, hempty]
      exact (hn hn0).elim
    · exact Or.inr ⟨b :: pre, by simp [hprefix]⟩

/-- The parser's mathematical canonicality condition is exact: an empty
    block or one ending in one is precisely a canonical `Nat.bits` block. -/
theorem canonical_digits_iff (digits : List Bool) :
    (digits = [] ∨ ∃ pre, digits = pre ++ [true]) ↔ ∃ n : ℕ, n.bits = digits := by
  constructor
  · intro h
    rcases h with rfl | ⟨pre, rfl⟩
    · exact ⟨0, by simp⟩
    · exact ⟨bitsValue (pre ++ [true]), bitsValue_bits_append_true pre⟩
  · rintro ⟨n, rfl⟩
    exact nat_bits_canonical n

end TensorCanonicalDigits


open CookPvsNP ProjSchedTW.Complexity

namespace CookPvsNP.CanonicalBlockParser

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
theorem parseBlockProg_success (digits : List Bool) (tail acc status : List BSym) :
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
theorem parseBlockProg_reject_minus (digits : List Bool) (tail acc status : List BSym) :
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
theorem parseBlockProg_reject_eof (digits : List Bool) (acc status : List BSym) :
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
theorem parseCanonicalBlockProg_accept (digits : List Bool) (tail status : List BSym)
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
theorem parseCanonicalBlockProg_reject_high_zero (pre : List Bool) (tail status : List BSym) :
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
theorem parseCanonicalBlockProg_reject_minus (digits : List Bool) (tail status : List BSym) :
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
theorem parseCanonicalBlockProg_reject_eof (digits : List Bool) (status : List BSym) :
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

end CookPvsNP.CanonicalBlockParser

namespace CookPvsNP.CanonicalBlockParser

/-- Every actual canonical `encNat` block is accepted by the concrete parser,
    with the exact same separator handling and step bound as above. -/
theorem parseCanonicalBlockProg_encNat (n : ℕ) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (encNat n ++ tail) [] status)
      (store tail (n.bits.map digitSym).reverse (BSym.one :: BSym.one :: status))
      (3 * n.bits.length + 7) := by
  have hmap : (n.bits.map fun b ↦ if b then BSym.one else BSym.zero) =
      n.bits.map digitSym := by
    apply List.map_congr_left
    intro b hb
    cases b <;> rfl
  have hcode : encNat n ++ tail = n.bits.map digitSym ++ BSym.sep :: tail := by
    simp only [encNat, List.append_assoc, List.singleton_append, hmap]
  rw [hcode]
  exact parseCanonicalBlockProg_accept n.bits tail status (TensorCanonicalDigits.nat_bits_canonical n)

/-- The parser's exact cost on an actual natural-number code is linear in
    the complete input length, including any trailing suffix. -/
theorem parseCanonicalBlockProg_encNat_linear (n : ℕ) (tail status : List BSym) :
    ∃ steps, parseCanonicalBlockProg.Exec
      (store (encNat n ++ tail) [] status)
      (store tail (n.bits.map digitSym).reverse (BSym.one :: BSym.one :: status)) steps ∧
      steps ≤ 3 * (encNat n ++ tail).length + 7 := by
  refine ⟨3 * n.bits.length + 7, parseCanonicalBlockProg_encNat n tail status, ?_⟩
  simp only [encNat, List.length_append, List.length_map, List.length_singleton]
  omega

end CookPvsNP.CanonicalBlockParser

namespace CookPvsNP.CanonicalBlockParser

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
theorem parseCanonicalBlockProg_total (input status : List BSym) :
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

/-- On every input, the parser terminates with at most one output digit for
    each input symbol, including malformed and truncated encodings. -/
theorem parseCanonicalBlockProg_total_both_lengths (input status : List BSym) :
    ∃ rest digits outstatus steps,
      parseCanonicalBlockProg.Exec (store input [] status) (store rest digits outstatus) steps ∧
      steps ≤ 3*input.length+7 ∧ digits.length ≤ input.length ∧ rest.length ≤ input.length := by
  obtain ⟨digits, stop, hw, hstop⟩ := split_digit_prefix input
  subst input
  have hbound : 3*digits.length+7 ≤ 3*(digits.map digitSym ++ stop).length+7 := by
    simp only [List.length_append, List.length_map]
    omega
  have hlen : (digits.map digitSym).reverse.length ≤ (digits.map digitSym ++ stop).length := by
    simp only [List.length_reverse, List.length_map, List.length_append]
    omega
  rcases hstop with hempty | ⟨tail, hsep⟩ | ⟨tail, hminus⟩
  · subst stop
    refine ⟨[], (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, ?_, hbound, hlen, by simp⟩
    simpa using parseCanonicalBlockProg_reject_eof digits status
  · subst stop
    rcases digit_end_cases digits with hempty | ⟨pre, htrue⟩ | ⟨pre, hfalse⟩
    · exact ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status,
        3*digits.length+7, parseCanonicalBlockProg_accept digits tail status (Or.inl hempty), hbound, hlen, by simp <;> omega⟩
    · exact ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status,
        3*digits.length+7, parseCanonicalBlockProg_accept digits tail status (Or.inr ⟨pre, htrue⟩), hbound, hlen, by simp <;> omega⟩
    · subst digits
      exact ⟨tail, ((pre ++ [false]).map digitSym).reverse, .zero :: .one :: status,
        3*(pre ++ [false]).length+7, parseCanonicalBlockProg_reject_high_zero pre tail status, hbound, hlen, by simp <;> omega⟩
  · subst stop
    exact ⟨.minus :: tail, (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, parseCanonicalBlockProg_reject_minus digits tail status, hbound, hlen, by simp <;> omega⟩


end CookPvsNP.CanonicalBlockParser

open CookPvsNP.CanonicalBlockParser

theorem solution :
    (∀ (n : ℕ) (tail status : List BSym),
      parseCanonicalBlockProg.Exec
        (store (encNat n ++ tail) [] status)
        (store tail (n.bits.map digitSym).reverse (.one :: .one :: status))
        (3 * n.bits.length + 7)) ∧
    (∀ input status : List BSym, ∃ rest digits outstatus steps,
      parseCanonicalBlockProg.Exec (store input [] status) (store rest digits outstatus) steps ∧
        steps ≤ 3 * input.length + 7 ∧ digits.length ≤ input.length ∧ rest.length ≤ input.length) := by
  constructor
  · exact parseCanonicalBlockProg_encNat
  · exact parseCanonicalBlockProg_total_both_lengths
