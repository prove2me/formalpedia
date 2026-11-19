-- Prove2me | solution 1 for FourToOneGames.four_to_one_perfect_completeness
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:55:28.289105+00:00
-- url     : https://prove2.me/submissions/5c0e1e52-49db-4462-90e4-3c7108aab6f7

import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_StackProgPortLift_liftProgC_exec
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Tactic.Omega
import Definitions.Def_CookPvsNP_StackModel
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Sort
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_FourToOneGames_LabelCover
import Definitions.Def_PerfectCompleteness
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_PricingWithTips3DM_d8886977e67d59ff4f35de9d
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.IntervalCases
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fin.Embedding
import Theorems.Thm_CookPvsNP_unary_to_encNat_stack
import Theorems.Thm_OAI_PerfectCompleteness_Theorem11_exists_reduction

/- WordMachines -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines

open CookPvsNP

variable {K A : Type} [DecidableEq K] [DecidableEq A]

/-- A run of unary tokens, followed by one separator. -/
def unary (token stop : A) (n : ℕ) : List A :=
  List.replicate n token ++ [stop]

/-- Read unary tokens from the input. If requested, accumulate them on a second tape. -/
def scan (src : K) (dst : Option K) (token : A) : StackProg K A :=
  .loop (fun h => decide (h src = some token))
    (.act (fun _ k => if k = src then .pop else if dst = some k then .push token else .keep))

def field (src : K) (dst : Option K) (token : A) : StackProg K A :=
  .seq (scan src dst token) (popProg src)

theorem scan_exec (src : K) (dst : Option K) (token : A) (n : ℕ) (tail : List A)
    (s : K → List A) (hs : s src = List.replicate n token ++ tail)
    (ht : tail.head? ≠ some token) :
    (scan src dst token).Exec s
      (fun k => if k = src then tail else if dst = some k then List.replicate n token ++ s k else s k)
      (3 * n + 1) := by
  induction n generalizing s with
  | zero =>
      convert StackProg.Exec.loopFalse (p := .act
        (fun _ k => if k = src then StackAct.pop
          else if dst = some k then .push token else .keep))
        (s := s) (test := fun h => decide (h src = some token))
        (by simpa [hs] using ht) using 1 <;>
        first | rfl | exact funext (fun k => by by_cases hk : k = src <;> simp_all)
  | succ n ih =>
      let mid := fun k => if k = src then List.replicate n token ++ tail
        else if dst = some k then token :: s k else s k
      have hg : decide ((s src).head? = some token) = true := by
        simp [hs, List.replicate_succ]
      have he : (StackProg.act
          (fun _ k => if k = src then StackAct.pop
            else if dst = some k then .push token else .keep)).Exec s mid 1 := by
        convert StackProg.Exec.act _ s using 1
        exact funext (fun k => by by_cases hk : k = src <;> by_cases hd : dst = some k <;> simp [mid, StackProg.applyAct, StackAct.apply, hk, hd, hs, List.replicate_succ])
      have hmid : mid src = List.replicate n token ++ tail := by simp [mid]
      have hr := StackProg.Exec.loopTrue hg he (ih mid hmid)
      convert hr using 1 <;>
        first | rfl | omega |
          exact funext (fun k => by by_cases hk : k = src <;>
            by_cases hd' : dst = some k <;>
            simp [mid, hk, hd', List.replicate_succ'])


omit [DecidableEq A] in
theorem pop_exec (src : K) (s : K → List A) :
    (popProg src).Exec s (Function.update s src (s src).tail) 1 := by
  convert StackProg.Exec.act _ s using 1 <;>
    first | rfl | exact funext (fun k => by
      by_cases hk : k = src <;> simp [StackProg.applyAct, StackAct.apply, hk])

theorem field_exec (src : K) (dst : Option K) (token stop : A) (n : ℕ)
    (tail : List A) (s : K → List A) (hs : s src = unary token stop n ++ tail)
    (ht : stop ≠ token) :
    (field src dst token).Exec s
      (fun k => if k = src then tail else if dst = some k then List.replicate n token ++ s k else s k)
      (3 * n + 3) := by
  let mid := fun k => if k = src then stop :: tail
    else if dst = some k then List.replicate n token ++ s k else s k
  have hscan : (scan src dst token).Exec s mid (3 * n + 1) :=
    scan_exec src dst token n (stop :: tail) s (by simpa [unary] using hs) (by simpa using ht)
  have hp := hscan.seq (pop_exec src mid)
  convert hp using 1 <;>
    first | rfl | omega | exact funext (fun k => by by_cases hk : k = src <;> simp [mid, hk])

/-- Skip one separator-terminated field for each token on the index tape. -/
def skipFields (src index : K) (token : A) : StackProg K A :=
  .loop (fun h => (h index).isSome) (.seq (field src none token) (popProg index))

theorem skipFields_exec (src index : K) (token stop : A) (ns : List ℕ) (tail : List A)
    (s : K → List A) (ht : stop ≠ token) (hi : index ≠ src)
    (hs : s src = ns.flatMap (unary token stop) ++ tail)
    (hn : (s index).length = ns.length) :
    (skipFields src index token).Exec s
      (Function.update (Function.update s src tail) index [])
      (3 * (ns.flatMap (unary token stop)).length + 4 * ns.length + 1) := by
  induction ns generalizing s with
  | nil =>
      have hEmpty : s index = [] := List.length_eq_zero_iff.mp (by simpa using hn)
      convert StackProg.Exec.loopFalse (p := .seq (field src none token) (popProg index))
        (s := s) (test := fun h => (h index).isSome) (by simp [hEmpty]) using 1 <;>
        first | rfl | exact funext (fun k => by
          by_cases hk : k = index <;> by_cases hks : k = src <;> simp_all)
  | cons n ns ih =>
      let rest := ns.flatMap (unary token stop) ++ tail
      let mid := Function.update s src rest
      let next := Function.update mid index (s index).tail
      have hf : (field src none token).Exec s mid (3 * n + 3) := by
        convert
          field_exec src none token stop n rest s (by simpa [rest, List.append_assoc] using hs) ht
            using 1
        exact funext (fun k => by by_cases hk : k = src <;> simp [mid, hk])
      have hp : (popProg index).Exec mid next 1 := by
        simpa [next, mid, hi] using pop_exec index mid
      have hg : ((s index).head?).isSome = true := by
        cases h : s index <;> simp_all
      have hn' : (next index).length = ns.length := by
        simp [next, List.length_tail, hn]
      have hs' : next src = rest := by simp [next, mid, Ne.symm hi]
      have hr := StackProg.Exec.loopTrue hg (hf.seq hp) (ih next hs' hn')
      convert hr using 1 <;>
        first | rfl | (simp [unary]; omega) |
          exact funext (fun k => by by_cases hk : k = index <;>
            by_cases hks : k = src <;> simp [next, mid, hk, hks, Ne.symm hi])


omit [DecidableEq A] in
theorem clear_exec (src : K) (s : K → List A) :
    (clearProg src).Exec s (Function.update s src []) (3 * (s src).length + 1) := by
  unfold clearProg
  convert stack_transfer src (fun _ => false) s using 1
  exact funext (fun k => by by_cases hk : k = src <;> simp [transferStore, hk])

private def lookupState (w ix out work count : List A) : Fin 6 → List A :=
  ![w, ix, out, work, count, []]

/-- Read a field into the output tape, preserving the table and index tapes. -/
def lookupField (token : A) : StackProg (Fin 6) A :=
  .seq (copyProg 0 3 5) (.seq (copyProg 1 4 5)
    (.seq (skipFields 3 4 token) (.seq (field 3 (some 2) token) (clearProg 3))))

def lookupStore (w ix out : List A) : Fin 6 → List A := lookupState w ix out [] []

theorem lookupField_exec (token stop : A) (w ix out : List A)
    (previous : List ℕ) (n : ℕ) (tail : List A) (ht : stop ≠ token)
    (hw : w = previous.flatMap (unary token stop) ++ unary token stop n ++ tail)
    (hi : ix.length = previous.length) :
    ∃ t, (lookupField token).Exec (lookupStore w ix out)
      (lookupStore w ix (List.replicate n token ++ out)) t ∧
      t ≤ 10 * w.length + 10 * ix.length + 15 := by
  let src := lookupStore w ix out
  let first := lookupState w ix out w []
  let second := lookupState w ix out w ix
  let third := lookupState w ix out (unary token stop n ++ tail) []
  let fourth := lookupState w ix (List.replicate n token ++ out) tail []
  have hcopy1 : (copyProg (0 : Fin 6) 3 5).Exec src first (6 * w.length + 3) := by
    convert stack_copy (0 : Fin 6) 3 5 (by decide) (by decide) (by decide) src rfl using 1 <;>
      first | rfl | exact funext (fun k => by
        fin_cases k <;> simp [first, src, lookupStore, lookupState])
  have hcopy2 : (copyProg (1 : Fin 6) 4 5).Exec first second (6 * ix.length + 3) := by
    convert stack_copy (1 : Fin 6) 4 5 (by decide) (by decide) (by decide) first rfl using 1 <;>
      first | rfl | exact funext (fun k => by
        fin_cases k <;> simp [second, first, lookupState])
  have hskip : (skipFields (3 : Fin 6) 4 token).Exec second third
      (3 * (previous.flatMap (unary token stop)).length + 4 * previous.length + 1) := by
    convert skipFields_exec (3 : Fin 6) 4 token stop previous (unary token stop n ++ tail)
      second ht (by decide) (by simpa [second, lookupState, List.append_assoc] using hw) hi using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have hfield : (field (3 : Fin 6) (some 2) token).Exec third fourth (3 * n + 3) := by
    convert field_exec (3 : Fin 6) (some 2) token stop n tail third rfl ht using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have hclear : (clearProg (3 : Fin 6)).Exec fourth
      (lookupStore w ix (List.replicate n token ++ out)) (3 * tail.length + 1) := by
    convert clear_exec (3 : Fin 6) fourth using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl)
  refine ⟨_, hcopy1.seq (hcopy2.seq (hskip.seq (hfield.seq hclear))), ?_⟩
  have hlength := congrArg List.length hw
  simp only [List.length_append, unary, List.length_replicate, List.length_singleton] at hlength
  omega


/-- Select the field named by the length of the index tape. -/
theorem lookupField_at (token stop : A) (ns : List ℕ) (ix out : List A)
    (ht : stop ≠ token) (hi : ix.length < ns.length) :
    ∃ t, (lookupField token).Exec (lookupStore (ns.flatMap (unary token stop)) ix out)
      (lookupStore (ns.flatMap (unary token stop)) ix
        (List.replicate ns[ix.length] token ++ out)) t ∧
      t ≤ 10 * (ns.flatMap (unary token stop)).length + 10 * ix.length + 15 := by
  apply lookupField_exec token stop _ ix out (ns.take ix.length)
    ns[ix.length] ((ns.drop (ix.length + 1)).flatMap (unary token stop)) ht
  · have h := congrArg (List.flatMap (unary token stop)) (List.take_append_drop ix.length ns)
    rw [List.drop_eq_getElem_cons hi] at h
    simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using h.symm
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]


/-- Load four leading unary parameters and leave the rest on the input tape. -/
def readFour (token : A) : StackProg (Fin 5) A :=
  .seq (field 0 (some 1) token) (.seq (field 0 (some 2) token)
    (.seq (field 0 (some 3) token) (field 0 (some 4) token)))

theorem readFour_exec (token stop : A) (ht : stop ≠ token)
    (a b c d : ℕ) (rest : List A) :
    (readFour token).Exec
      ![([a, b, c, d].flatMap (unary token stop)) ++ rest, [], [], [], []]
      ![rest, List.replicate a token, List.replicate b token,
        List.replicate c token, List.replicate d token]
      (3 * (a + b + c + d) + 15) := by
  let code := unary token stop
  let s0 : Fin 5 → List A := ![code a ++ (code b ++ (code c ++ (code d ++ rest))), [], [], [], []]
  let s1 : Fin 5 → List A := ![code b ++ (code c ++ (code d ++ rest)),
    List.replicate a token, [], [], []]
  let s2 : Fin 5 → List A := ![code c ++ (code d ++ rest),
    List.replicate a token, List.replicate b token, [], []]
  let s3 : Fin 5 → List A := ![code d ++ rest,
    List.replicate a token, List.replicate b token, List.replicate c token, []]
  have h1 : (field (0 : Fin 5) (some 1) token).Exec s0 s1 (3 * a + 3) := by
    convert field_exec (0 : Fin 5) (some 1) token stop a
      (code b ++ (code c ++ (code d ++ rest))) s0 rfl ht using 1
    exact funext (fun k => by fin_cases k <;> simp [s0, s1])
  have h2 : (field (0 : Fin 5) (some 2) token).Exec s1 s2 (3 * b + 3) := by
    convert field_exec (0 : Fin 5) (some 2) token stop b
      (code c ++ (code d ++ rest)) s1 rfl ht using 1
    exact funext (fun k => by fin_cases k <;> simp [s1, s2])
  have h3 : (field (0 : Fin 5) (some 3) token).Exec s2 s3 (3 * c + 3) := by
    convert field_exec (0 : Fin 5) (some 3) token stop c (code d ++ rest) s2 rfl ht using 1
    exact funext (fun k => by fin_cases k <;> simp [s2, s3])
  have h4 : (field (0 : Fin 5) (some 4) token).Exec s3
      ![rest, List.replicate a token, List.replicate b token,
        List.replicate c token, List.replicate d token] (3 * d + 3) := by
    convert field_exec (0 : Fin 5) (some 4) token stop d rest s3 rfl ht using 1
    exact funext (fun k => by fin_cases k <;> simp [s3])
  convert h1.seq (h2.seq (h3.seq h4)) using 1 <;>
    first | rfl | omega | simp [s0, code, List.append_assoc]


/-- Move exactly as many symbols as there are index tokens, reversing onto the destination. -/
def reversePrefix (src index dst : K) : StackProg K A :=
  .loop (fun h => (h index).isSome)
    (.act fun h k => if k = index then .pop else transferAct src (fun j => decide (j = dst)) h k)

omit [DecidableEq A] in
theorem reversePrefix_exec (src index dst : K) (his : index ≠ src)
    (hdi : dst ≠ index) (hds : dst ≠ src)
    (xs rest : List A) (s : K → List A) (hs : s src = xs ++ rest)
    (hi : (s index).length = xs.length) :
    (reversePrefix src index dst).Exec s
      (Function.update (Function.update (Function.update s src rest) index []) dst
        (xs.reverse ++ s dst))
      (3 * xs.length + 1) := by
  induction xs generalizing s with
  | nil =>
      have hEmpty : s index = [] := List.length_eq_zero_iff.mp (by simpa using hi)
      convert StackProg.Exec.loopFalse
        (p := .act fun h k => if k = index then .pop
          else transferAct src (fun j => decide (j = dst)) h k)
        (s := s) (test := fun h => (h index).isSome) (by simp [hEmpty]) using 1 <;>
        first | rfl | exact funext (fun k => by by_cases hk : k = index <;>
          by_cases hks : k = src <;> by_cases hkd : k = dst <;> simp_all)
  | cons a xs ih =>
      let next := Function.update
        (Function.update (Function.update s src (xs ++ rest)) index (s index).tail)
        dst (a :: s dst)
      have hn : next src = xs ++ rest := by simp [next, Ne.symm his, Ne.symm hds]
      have hi' : (next index).length = xs.length := by
        simp [next, Ne.symm hdi, List.length_tail, hi]
      have hg : (s index).head?.isSome = true := by cases h : s index <;> simp_all
      have ha : (StackProg.act fun h k => if k = index then .pop
          else transferAct src (fun j => decide (j = dst)) h k).Exec s next 1 := by
        convert StackProg.Exec.act _ s using 1
        exact funext (fun k => by by_cases hki : k = index <;> by_cases hks : k = src <;>
          by_cases hkd : k = dst <;>
          simp_all [next, StackProg.applyAct, transferAct, StackAct.apply])
      have hr := StackProg.Exec.loopTrue hg ha (ih next hn hi')
      convert hr using 1 <;>
        first | rfl | (simp; omega) | exact funext (fun k => by
          by_cases hki : k = index <;> by_cases hks : k = src <;> by_cases hkd : k = dst <;>
          simp_all [next, Ne.symm his, Ne.symm hdi, Ne.symm hds, List.append_assoc])

/-- Split the raw payload at a length given by the index tape. -/
def splitPrefix : StackProg (Fin 6) A :=
  .seq (copyProg 1 4 5) (.seq (reversePrefix 0 4 3)
    (transferProg 3 (fun k => decide (k = 2))))

omit [DecidableEq A] in
theorem splitPrefix_exec (xs rest ix out : List A) (hi : ix.length = xs.length) :
    splitPrefix.Exec (lookupStore (xs ++ rest) ix out)
      (lookupStore rest ix (xs ++ out)) (12 * xs.length + 7) := by
  let s := lookupStore (xs ++ rest) ix out
  let m := lookupState (xs ++ rest) ix out [] ix
  let n := lookupState rest ix out xs.reverse []
  have hc : (copyProg (1 : Fin 6) 4 5).Exec s m (6 * ix.length + 3) := by
    convert stack_copy (1 : Fin 6) 4 5 (by decide) (by decide) (by decide) s rfl using 1 <;>
      first | rfl | exact funext (fun k => by
        fin_cases k <;> simp [m, s, lookupStore, lookupState])
  have hr : (reversePrefix (0 : Fin 6) 4 3).Exec m n (3 * xs.length + 1) := by
    convert reversePrefix_exec (0 : Fin 6) 4 3 (by decide) (by decide) (by decide)
      xs rest m rfl hi using 1
    exact funext (fun k => by fin_cases k <;> simp [n, m, lookupState])
  have ht : (transferProg (3 : Fin 6) (fun k => decide (k = 2))).Exec n
      (lookupStore rest ix (xs ++ out)) (3 * xs.length + 1) := by
    convert stack_transfer (3 : Fin 6) (fun k => decide (k = 2)) n using 1 <;>
      first | rfl |
        solve | simp [n, lookupState] |
        exact funext (fun k => by fin_cases k <;> simp [n, lookupState, lookupStore, transferStore])
  convert hc.seq (hr.seq ht) using 1 <;> first | rfl | omega


private def multiplyPorts : Fin 4 ↪ Fin 5 := ⟨![0, 2, 3, 4], by decide⟩

/-- Append the product of two unary lengths to a destination tape. -/
def multiply : StackProg (Fin 5) A :=
  .seq (copyProg 1 3 4) (repeatCopyProg multiplyPorts)

omit [DecidableEq A] in
theorem multiply_exec (token : A) (a b : ℕ) (out : List A) :
    multiply.Exec
      ![List.replicate a token, List.replicate b token, out, [], []]
      ![List.replicate a token, List.replicate b token,
        List.replicate (a*b) token ++ out, [], []]
      ((6*a+13)*b+5) := by
  let src : Fin 5 → List A := ![List.replicate a token, List.replicate b token, out, [], []]
  let mid : Fin 5 → List A :=
    ![List.replicate a token, List.replicate b token, out, List.replicate b token, []]
  have hc : (copyProg (1 : Fin 5) 3 4).Exec src mid (6 * b + 3) := by
    convert stack_copy (1 : Fin 5) 3 4 (by decide) (by decide) (by decide) src rfl using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> simp [mid, src]) |
        solve | simp [src]
  have hr : (repeatCopyProg multiplyPorts).Exec mid
      ![List.replicate a token, List.replicate b token, List.replicate (a*b) token ++ out, [], []]
      ((6 * a + 7) * b + 1) := by
    convert stack_repeat_copy multiplyPorts mid rfl using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;>
        simp [mid, multiplyPorts, Nat.mul_comm]) |
        solve | simp [mid, multiplyPorts]
  convert hc.seq hr using 1 <;> first | rfl | (simp only [Nat.add_mul]; omega)


private noncomputable def decodePort {L : Type} (r : K ↪ L) (l : L) : Option K := by
  classical
  exact if h : ∃ k, r k = l then some (Classical.choose h) else none

omit [DecidableEq K] in
private theorem decodePort_spec {L : Type} (r : K ↪ L) (l : L) (k : K) :
    decodePort r l = some k ↔ r k = l := by
  classical
  unfold decodePort
  split
  · rename_i h
    exact ⟨fun h' => (congrArg r (Option.some.inj h')).symm.trans (Classical.choose_spec h),
      fun hr => congrArg some (r.injective ((Classical.choose_spec h).trans hr.symm))⟩
  · rename_i h
    exact ⟨(fun h' => by cases h'), fun hr => (h ⟨k, hr⟩).elim⟩

/-- Run a verified subprogram on selected ports and preserve the remaining tapes. -/
noncomputable def onPorts {L : Type} (r : K ↪ L) (p : StackProg K A) : StackProg L A :=
  StackProgPortLift.liftProgC r (decodePort r) p

omit [DecidableEq K] [DecidableEq A] in
theorem onPorts_exec {L : Type} (r : K ↪ L) {p : StackProg K A} {n : ℕ}
    {s t : K → List A} {base final : L → List A} (h : p.Exec s t n)
    (hs : ∀ k, base (r k) = s k) (ht : ∀ k, final (r k) = t k)
    (hf : ∀ l, (∀ k, r k ≠ l) → final l = base l) :
    (onPorts r p).Exec base final n := by
  classical
  have he := StackProgPortLift.liftProgC_exec r (decodePort r) (decodePort_spec r) h base (funext hs)
  unfold onPorts
  convert he using 1
  exact funext (fun l => by
    unfold StackProgPortLift.write
    split
    · rename_i hex
      exact (congrArg final (Classical.choose_spec hex)).symm.trans (ht (Classical.choose hex))
    · rename_i hn
      exact hf l (fun k hk => hn ⟨k, hk⟩))

private theorem falseRun (xs : List Bool) :
    ∃ n tail, xs = List.replicate n false ++ tail ∧
      tail.head? ≠ some false ∧ xs.any id = tail.head?.isSome := by
  induction xs with
  | nil => exact ⟨0, [], rfl, by simp, rfl⟩
  | cons b xs ih =>
      cases b
      · obtain ⟨n, tail, hx, hh, ha⟩ := ih
        exact ⟨n+1, tail, by simp [List.replicate_succ, ← hx], hh, by simpa using ha⟩
      · exact ⟨0, true :: xs, rfl, by simp, by simp⟩

private def emitSeen (h : Fin 4 → Option Bool) (k : Fin 4) : StackAct Bool :=
  if k = 1 then .push (h 2).isSome else .keep

/-- Compute whether a Boolean tape contains a true bit while preserving that tape. -/
def anyTrue : StackProg (Fin 4) Bool :=
  .seq (copyProg 0 2 3) (.seq (scan 2 none false) (.seq (.act emitSeen) (clearProg 2)))

theorem anyTrue_exec (xs out : List Bool) :
    ∃ t, anyTrue.Exec ![xs, out, [], []] ![xs, xs.any id :: out, [], []] t ∧
      t ≤ 9 * xs.length + 9 := by
  obtain ⟨n, tail, hx, hh, ha⟩ := falseRun xs
  let s0 : Fin 4 → List Bool := ![xs, out, [], []]
  let s1 : Fin 4 → List Bool := ![xs, out, xs, []]
  let s2 : Fin 4 → List Bool := ![xs, out, tail, []]
  let s3 : Fin 4 → List Bool := ![xs, xs.any id :: out, tail, []]
  let s4 : Fin 4 → List Bool := ![xs, xs.any id :: out, [], []]
  have hc : (copyProg (0 : Fin 4) 2 3).Exec s0 s1 (6*xs.length+3) := by
    convert stack_copy (0 : Fin 4) 2 3 (by decide) (by decide) (by decide) s0 rfl using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> simp [s0, s1])
  have hs : (scan (2 : Fin 4) none false).Exec s1 s2 (3*n+1) := by
    convert scan_exec (2 : Fin 4) none false n tail s1 hx hh using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have he : (StackProg.act emitSeen).Exec s2 s3 1 := by
    convert StackProg.Exec.act emitSeen s2 using 1
    exact funext (fun k => by fin_cases k <;> simp [s2, s3, StackProg.applyAct, emitSeen, StackAct.apply, ha])
  have hf : (clearProg (2 : Fin 4)).Exec s3 s4 (3*tail.length+1) := by
    convert clear_exec (2 : Fin 4) s3 using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl)
  refine ⟨_, hc.seq (hs.seq (he.seq hf)), ?_⟩
  have hlen := congrArg List.length hx
  simp only [List.length_append, List.length_replicate] at hlen
  omega

end FourToOneGames.WordMachines

end

/- Bridge -/
section

set_option autoImplicit false

open Turing CookPvsNP

namespace StackTM2Bridge

variable {K A Q : Type} [DecidableEq K]

abbrev Heads (K A : Type) := K → Option A
abbrev Statement (K A Q : Type) := TM2.Stmt (fun _ : K => A) (Option Q) (Heads K A)

/-- Capture the selected stack tops in finite internal storage. -/
def readHeads (ks : List K) (next : Statement K A Q) : Statement K A Q :=
  ks.foldr (fun k rest => .peek k (fun h top => Function.update h k top) rest) next

/-- The heads captured by a finite list of peek instructions. -/
def capturedHeads (ks : List K) (h : Heads K A) (s : K → List A) : Heads K A :=
  fun k => if k ∈ ks then (s k).head? else h k

theorem readHeads_stepAux (ks : List K) (next : Statement K A Q)
    (h : Heads K A) (s : K → List A) :
    TM2.stepAux (readHeads ks next) h s =
      TM2.stepAux next (capturedHeads ks h s) s := by
  induction ks generalizing h with
  | nil => rfl
  | cons k ks ih =>
    change TM2.stepAux (readHeads ks next) (Function.update h k (s k).head?) s = _
    rw [ih]
    congr 1
    funext j
    by_cases hj : j ∈ ks <;> by_cases hkj : j = k <;> simp [capturedHeads, hj, hkj]

/-- Execute one selected action without changing the saved heads. -/
def oneAction [Inhabited A] (k : K)
    (act : Heads K A → K → StackAct A) (next : Statement K A Q) : Statement K A Q :=
  .branch (fun h => match act h k with | .keep => true | _ => false) next
    (.branch (fun h => match act h k with | .pop => true | _ => false)
      (.pop k (fun h _ => h) next)
      (.push k (fun h => match act h k with | .push a => a | _ => default) next))

/-- Apply one action at every selected port, using the original saved heads. -/
def applyActions [Inhabited A] (ks : List K)
    (act : Heads K A → K → StackAct A) (next : Statement K A Q) : Statement K A Q :=
  ks.foldr (fun k rest => oneAction k act rest) next

/-- Functional meaning of the finite sequence of action instructions. -/
def applyStores (ks : List K) (act : K → StackAct A) (s : K → List A) : K → List A :=
  ks.foldl (fun t k => Function.update t k ((act k).apply (t k))) s

theorem oneAction_stepAux [Inhabited A] (k : K)
    (act : Heads K A → K → StackAct A) (next : Statement K A Q)
    (h : Heads K A) (s : K → List A) :
    TM2.stepAux (oneAction k act next) h s =
      TM2.stepAux next h (Function.update s k ((act h k).apply (s k))) := by
  cases ha : act h k <;> simp [oneAction, TM2.stepAux, ha, StackAct.apply]

theorem applyActions_stepAux [Inhabited A] (ks : List K)
    (act : Heads K A → K → StackAct A) (next : Statement K A Q)
    (h : Heads K A) (s : K → List A) :
    TM2.stepAux (applyActions ks act next) h s =
      TM2.stepAux next h (applyStores ks (act h) s) := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    change TM2.stepAux (oneAction k act (applyActions ks act next)) h s = _
    rw [oneAction_stepAux, ih]
    rfl

theorem applyStores_eq (ks : List K) (hn : ks.Nodup)
    (act : K → StackAct A) (s : K → List A) :
    applyStores ks act s =
      fun k => if k ∈ ks then (act k).apply (s k) else s k := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    rw [List.nodup_cons] at hn
    change applyStores ks act (Function.update s k ((act k).apply (s k))) = _
    rw [ih hn.2]
    funext j
    by_cases hj : j = k <;> simp [hj, hn.1]

variable [Fintype K]

theorem readHeads_all_stepAux (next : Statement K A Q)
    (h : Heads K A) (s : K → List A) :
    TM2.stepAux (readHeads (Finset.univ : Finset K).toList next) h s =
      TM2.stepAux next (fun k => (s k).head?) s := by
  rw [readHeads_stepAux]
  congr 1
  funext k
  simp [capturedHeads]

theorem applyActions_all_stepAux [Inhabited A]
    (act : Heads K A → K → StackAct A) (next : Statement K A Q)
    (h : Heads K A) (s : K → List A) :
    TM2.stepAux (applyActions (Finset.univ : Finset K).toList act next) h s =
      TM2.stepAux next h (fun k => (act h k).apply (s k)) := by
  rw [applyActions_stepAux, applyStores_eq _ (Finset.nodup_toList _)]
  congr 1
  funext k
  simp

/-- A source instruction captures all heads before applying its simultaneous actions. -/
noncomputable def sourceStatement [Inhabited A] (P : StackMachine K A Q) (q : Q) : Statement K A Q :=
  if P.done q then .goto (fun _ => none) else
    readHeads (Finset.univ : Finset K).toList
      (applyActions (Finset.univ : Finset K).toList (fun h => (P.next q h).2)
        (.goto (fun h => some (P.next q h).1)))

/-- The finite-stack source compiler, parameterized by its cleanup statement. -/
noncomputable def compileWithCleanup [Fintype A] [Fintype Q] [Inhabited A]
    (P : StackMachine K A Q) (ki ko : K) (cleanup : Statement K A Q) : FinTM2 where
  K := K
  k₀ := ki
  k₁ := ko
  Γ _ := A
  Λ := Option Q
  main := some P.initial
  σ := Heads K A
  initialState := fun _ => none
  m label := match label with
    | none => cleanup
    | some q => sourceStatement P q

/-- A nonhalting source instruction is exactly one target machine step. -/
theorem source_step [Fintype A] [Fintype Q] [Inhabited A]
    (P : StackMachine K A Q) (ki ko : K) (cleanup : Statement K A Q)
    (q : Q) (hq : P.done q = false) (h : Heads K A) (s : K → List A) :
    (compileWithCleanup P ki ko cleanup).step ⟨some (some q), h, s⟩ =
      some ⟨some (some (P.next q (fun k => (s k).head?)).1),
        (fun k => (s k).head?),
        (fun k => ((P.next q (fun j => (s j).head?)).2 k).apply (s k))⟩ := by
  change some (TM2.stepAux (sourceStatement P q) h s) = _
  simp only [sourceStatement, hq, Bool.false_eq_true, ↓reduceIte]
  rw [readHeads_all_stepAux, applyActions_all_stepAux]
  rfl

/-- A completed source state enters the cleanup label in one target step. -/
theorem done_step [Fintype A] [Fintype Q] [Inhabited A]
    (P : StackMachine K A Q) (ki ko : K) (cleanup : Statement K A Q)
    (q : Q) (hq : P.done q = true) (h : Heads K A) (s : K → List A) :
    (compileWithCleanup P ki ko cleanup).step ⟨some (some q), h, s⟩ =
      some ⟨some none, h, s⟩ := by
  change some (TM2.stepAux (sourceStatement P q) h s) = _
  simp only [sourceStatement, hq, ↓reduceIte, TM2.stepAux]
  rfl

end StackTM2Bridge

end

/- Cleanup -/
section

set_option autoImplicit false
open Turing CookPvsNP StackTM2Bridge

namespace StackTM2Cleanup
variable {K A Q : Type} [DecidableEq K] [Fintype K]

noncomputable def otherHeadsEmpty (ko : K) (h : Heads K A) : Bool :=
  (Finset.univ : Finset K).toList.all (fun k => if k = ko then true else (h k).isNone)

def poppedStore (ko : K) (s : K → List A) : K → List A :=
  fun k => if k = ko then s k else (s k).tail

noncomputable def cleanupStatement [Inhabited A] (ko : K) : Statement K A Q :=
  readHeads (Finset.univ : Finset K).toList
    (.branch (otherHeadsEmpty ko)
      (.load (fun _ => fun _ => none) .halt)
      (applyActions (Finset.univ : Finset K).toList
        (fun _ k => if k = ko then .keep else .pop)
        (.goto (fun _ => none))))

lemma cleanup_stepAux [Inhabited A] (ko : K) (h : Heads K A) (s : K → List A) :
    TM2.stepAux (cleanupStatement (Q := Q) ko) h s =
      if otherHeadsEmpty ko (fun k => (s k).head?) then
        ⟨none, (fun _ => none), s⟩
      else
        ⟨some none, (fun k => (s k).head?), poppedStore ko s⟩ := by
  rw [cleanupStatement, readHeads_all_stepAux]
  simp only [TM2.stepAux, applyActions_all_stepAux]
  cases otherHeadsEmpty ko (fun k => (s k).head?) <;> simp
  funext k
  by_cases hk : k = ko <;> simp [hk, poppedStore, StackAct.apply]

lemma otherHeadsEmpty_iff (ko : K) (s : K → List A) :
    otherHeadsEmpty ko (fun k => (s k).head?) = true ↔ ∀ k, k ≠ ko → s k = [] := by
  simp only [otherHeadsEmpty, List.all_eq_true, Finset.mem_toList, Finset.mem_univ, true_implies]
  exact ⟨fun h k hk => by simpa [hk] using h k,
    fun h k => by by_cases hk : k = ko <;> simp_all⟩

noncomputable def machine [Fintype A] [Fintype Q] [Inhabited A]
    (P : StackMachine K A Q) (ki ko : K) : FinTM2 :=
  compileWithCleanup P ki ko (cleanupStatement ko)

lemma cleanup_step [Fintype A] [Fintype Q] [Inhabited A]
    (P : StackMachine K A Q) (ki ko : K) (h : Heads K A) (s : K → List A) :
    (machine P ki ko).step ⟨some none, h, s⟩ =
      some (if otherHeadsEmpty ko (fun k => (s k).head?) then
        ⟨none, (fun _ => none), s⟩
      else
        ⟨some none, (fun k => (s k).head?), poppedStore ko s⟩) := by
  change some (TM2.stepAux (cleanupStatement ko) h s) = _
  rw [cleanup_stepAux]
  rfl

private def oneStep {C : Type} {f : C → Option C} {a b : C} (h : f a = some b) :
    StateTransition.EvalsToInTime f a (some b) 1 :=
  ⟨⟨1, by change f a = some b; exact h⟩, le_rfl⟩

lemma halt_eq [Fintype A] [Fintype Q] [Inhabited A]
    (P : StackMachine K A Q) (ki ko : K) (s : K → List A)
    (hs : ∀ k, k ≠ ko → s k = []) :
    (⟨none, (fun _ => none), s⟩ : (machine P ki ko).Cfg) = haltList (machine P ki ko) (s ko) := by
  unfold haltList
  congr 1
  funext k
  by_cases hk : k = ko <;> simp_all [machine, compileWithCleanup]
  rfl

private def timeMono {C : Type} {f : C → Option C} {a : C} {b : Option C}
    {m n : Nat} (h : StateTransition.EvalsToInTime f a b m) (hmn : m ≤ n) :
    StateTransition.EvalsToInTime f a b n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hmn⟩

noncomputable def cleanup_empty [Fintype A] [Fintype Q] [Inhabited A]
    (P : StackMachine K A Q) (ki ko : K) (h : Heads K A) (s : K → List A)
    (hs : ∀ k, k ≠ ko → s k = []) :
    StateTransition.EvalsToInTime (machine P ki ko).step ⟨some none, h, s⟩
      (some (haltList (machine P ki ko) (s ko))) 1 := by
  apply oneStep
  rw [cleanup_step, (otherHeadsEmpty_iff ko s).mpr hs]
  simp only [↓reduceIte]
  rw [halt_eq P ki ko s hs]


noncomputable def cleanup_run [Fintype A] [Fintype Q] [Inhabited A]
    (P : StackMachine K A Q) (ki ko : K) (H : Nat) (h : Heads K A) (s : K → List A)
    (hs : ∀ k, k ≠ ko → (s k).length ≤ H) :
    StateTransition.EvalsToInTime (machine P ki ko).step ⟨some none, h, s⟩
      (some (haltList (machine P ki ko) (s ko))) (H + 1) := by
  induction H generalizing h s with
  | zero =>
    apply cleanup_empty P ki ko h s
    intro k hk
    exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero (hs k hk))
  | succ H ih =>
    by_cases hc : otherHeadsEmpty ko (fun k => (s k).head?) = true
    · exact timeMono (cleanup_empty P ki ko h s ((otherHeadsEmpty_iff ko s).mp hc)) (by omega)
    · have hp : ∀ k, k ≠ ko → (poppedStore ko s k).length ≤ H := by
        intro k hk
        simp only [poppedStore, if_neg hk, List.length_tail]
        have := hs k hk
        omega
      have hr := ih (fun k => (s k).head?) (poppedStore ko s) hp
      have ho : poppedStore ko s ko = s ko := by simp [poppedStore]
      rw [ho] at hr
      exact StateTransition.EvalsToInTime.trans _ 1 (H + 1) _ _ _
        (oneStep (by rw [cleanup_step]; simp [hc]; rfl)) hr


noncomputable def finish_run [Fintype A] [Fintype Q] [Inhabited A]
    (P : StackMachine K A Q) (ki ko : K) (w : List A) (n : Nat)
    (q : Q) (h : Heads K A) (s : K → List A) (hq : P.done q = true)
    (hr : StateTransition.EvalsToInTime (machine P ki ko).step (initList (machine P ki ko) w)
      (some ⟨some (some q), h, s⟩) n)
    (hs : ∀ k, k ≠ ko → (s k).length ≤ w.length + n) :
    TM2OutputsInTime (machine P ki ko) w (some (s ko)) (2 * n + w.length + 2) := by
  have hd := oneStep (done_step P ki ko (cleanupStatement ko) q hq h s)
  have hc := cleanup_run P ki ko (w.length + n) h s hs
  have hdc := StateTransition.EvalsToInTime.trans _ 1 (w.length + n + 1) _ _ _ hd hc
  have hall := StateTransition.EvalsToInTime.trans _ n (w.length + n + 1 + 1) _ _ _ hr hdc
  exact timeMono hall (by omega)

end StackTM2Cleanup

end

/- Trace -/
section

set_option autoImplicit false
open CookPvsNP StackProg

namespace StackTM2Trace

theorem trace_append {K A Q : Type} (P : StackMachine K A Q) {n m : ℕ}
    {c d e : StackCfg K A Q} (h : StackTrace P n c d) (h' : StackTrace P m d e) :
    StackTrace P (n + m) c e := by
  induction h with
  | refl => simpa using h'
  | cons hd _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using StackTrace.cons hd (ih h')

theorem trace_map {K A Q R : Type} (P : StackMachine K A Q) (S : StackMachine K A R)
    (f : StackCfg K A Q → StackCfg K A R)
    (hf : ∀ c, P.done c.state = false → S.done (f c).state = false ∧ S.step (f c) = f (P.step c))
    {n : ℕ} {c d : StackCfg K A Q} (h : StackTrace P n c d) : StackTrace S n (f c) (f d) := by
  induction h with
  | refl => exact .refl _
  | @cons n c d hd ht ih =>
    exact .cons (hf c hd).1 ((hf c hd).2 ▸ ih)

theorem Exec_trace {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∃ l : p.Label, p.done l = true ∧
      StackTrace p.machine n ⟨p.entry, s⟩ ⟨l, t⟩ := by
  induction h with
  | act f s =>
    refine ⟨true, rfl, .cons rfl ?_⟩
    exact .refl _
  | @seq p q s t u n m hp hq ihp ihq =>
    obtain ⟨lp, hdp, htp⟩ := ihp
    obtain ⟨lq, hdq, htq⟩ := ihq
    have hleft := trace_map p.machine (p.seq q).machine
      (fun c => ⟨Sum.inl c.state, c.store⟩) (by
        intro c hc
        change p.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) htp
    have hright := trace_map q.machine (p.seq q).machine
      (fun c => ⟨Sum.inr c.state, c.store⟩) (by
        intro c hc
        change q.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) htq
    have htransfer : StackTrace (p.seq q).machine 1 ⟨Sum.inl lp, t⟩ ⟨Sum.inr q.entry, t⟩ := by
      apply StackTrace.cons rfl
      simpa [StackMachine.step, machine, done, next, hdp, StackAct.apply] using
        (StackTrace.refl (P := (p.seq q).machine) (⟨Sum.inr q.entry, t⟩))
    refine ⟨Sum.inr lq, hdq, ?_⟩
    exact trace_append (p.seq q).machine
      (trace_append (p.seq q).machine hleft htransfer) hright
  | @branchTrue test p q s t n ht hp ih =>
    obtain ⟨l, hd, hrun⟩ := ih
    have hbody := trace_map p.machine (StackProg.branch test p q).machine
      (fun c => ⟨some (Sum.inl c.state), c.store⟩) (by
        intro c hc
        change p.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) hrun
    refine ⟨some (.inl l), hd, ?_⟩
    rw [Nat.add_comm]
    apply StackTrace.cons rfl
    simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using hbody
  | @branchFalse test p q s t n ht hq ih =>
    obtain ⟨l, hd, hrun⟩ := ih
    have hbody := trace_map q.machine (StackProg.branch test p q).machine
      (fun c => ⟨some (Sum.inr c.state), c.store⟩) (by
        intro c hc
        change q.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) hrun
    refine ⟨some (.inr l), hd, ?_⟩
    rw [Nat.add_comm]
    apply StackTrace.cons rfl
    simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using hbody
  | @loopFalse test p s ht =>
    refine ⟨some none, rfl, .cons rfl ?_⟩
    simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using
      (StackTrace.refl (P := (StackProg.loop test p).machine) ⟨some none, s⟩)
  | @loopTrue test p s t u n m ht hp hloop ihp ihloop =>
    obtain ⟨l, hd, hrun⟩ := ihp
    obtain ⟨l', hd', hrest⟩ := ihloop
    have hbody := trace_map p.machine (StackProg.loop test p).machine
      (fun c => ⟨some (some c.state), c.store⟩) (by
        intro c hc
        change p.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) hrun
    have henter : StackTrace (StackProg.loop test p).machine (1 + n)
        ⟨none, s⟩ ⟨some (some l), t⟩ := by
      rw [Nat.add_comm]
      apply StackTrace.cons rfl
      simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using hbody
    have htransfer : StackTrace (StackProg.loop test p).machine 1 ⟨some (some l), t⟩ ⟨none, t⟩ := by
      apply StackTrace.cons rfl
      simpa [StackMachine.step, machine, done, next, hd, StackAct.apply] using
        (StackTrace.refl (P := (StackProg.loop test p).machine) ⟨none, t⟩)
    exact ⟨l', hd', trace_append (StackProg.loop test p).machine
      (trace_append (StackProg.loop test p).machine henter htransfer) hrest⟩

theorem act_length_le {A : Type} (a : StackAct A) (s : List A) :
    (a.apply s).length ≤ s.length + 1 := by
  exact match a with
    | .keep => Nat.le_succ _
    | .push _ => le_rfl
    | .pop => by simpa only [StackAct.apply, List.length_tail] using
        ((Nat.sub_le s.length 1).trans (Nat.le_succ s.length))

theorem step_store_length_le {K A Q : Type} (P : StackMachine K A Q)
    (c : StackCfg K A Q) (k : K) :
    ((P.step c).store k).length ≤ (c.store k).length + 1 := by
  unfold StackMachine.step
  split
  · exact Nat.le_succ _
  · exact act_length_le _ _

theorem store_length_le {K A Q : Type} {P : StackMachine K A Q} {n : ℕ}
    {c d : StackCfg K A Q} (h : StackTrace P n c d) :
    ∀ k, (d.store k).length ≤ (c.store k).length + n := by
  induction h with
  | refl c => simp
  | @cons n c d hd ht ih =>
    intro k
    exact (ih k).trans (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_le_add_right (step_store_length_le P c k) n))

theorem init_store_length_le {K A Q : Type} [DecidableEq K] (P : StackMachine K A Q)
    (ki : K) (w : List A) (k : K) :
    ((P.init ki w).store k).length ≤ w.length := by
  change (if k = ki then w else []).length ≤ w.length
  split <;> simp

theorem init_trace_store_length_le {K A Q : Type} [DecidableEq K]
    {P : StackMachine K A Q} {ki : K} {w : List A} {n : ℕ} {d : StackCfg K A Q}
    (h : StackTrace P n (P.init ki w) d) (k : K) :
    (d.store k).length ≤ w.length + n := by
  exact (store_length_le h k).trans (Nat.add_le_add_right (init_store_length_le P ki w k) n)

theorem Exec_store_length_le {K A : Type} {p : StackProg K A} {s t : K → List A}
    {n : ℕ} (h : p.Exec s t n) (k : K) : (t k).length ≤ (s k).length + n := by
  exact match Exec_trace h with
    | ⟨_, _, ht⟩ => store_length_le ht k

end StackTM2Trace

end

/- Lift -/
section

set_option autoImplicit false
open Turing CookPvsNP StateTransition StackTM2Bridge

namespace StackTM2Lift
variable {K A Q : Type} [DecidableEq K] [Fintype K] [Fintype A] [Fintype Q] [Inhabited A]

lemma source_step_cfg (P : StackMachine K A Q) (ki ko : K) (cleanup : Statement K A Q)
    (c : StackCfg K A Q) (hc : P.done c.state = false) (h : Heads K A) :
    (compileWithCleanup P ki ko cleanup).step ⟨some (some c.state), h, c.store⟩ =
      some ⟨some (some (P.step c).state), (fun k => (c.store k).head?), (P.step c).store⟩ := by
  have hp : P.step c = ⟨(P.next c.state (fun k => (c.store k).head?)).1,
      fun k => ((P.next c.state (fun j => (c.store j).head?)).2 k).apply (c.store k)⟩ := by
    simp [StackMachine.step, hc]
  exact (source_step P ki ko cleanup c.state hc h c.store).trans
    (congrArg (fun e : StackCfg K A Q =>
      some (⟨some (some e.state), (fun k => (c.store k).head?), e.store⟩ :
        (compileWithCleanup P ki ko cleanup).Cfg)) hp.symm)

/-- Each source transition is one actual TM2 transition, with arbitrary incoming saved heads. -/
theorem source_trace_iterate (P : StackMachine K A Q) (ki ko : K) (cleanup : Statement K A Q)
    {n : ℕ} {c d : StackCfg K A Q} (hc : StackTrace P n c d) :
    ∀ initialHeads : Heads K A, ∃ finalHeads : Heads K A,
      ((fun z : Option (compileWithCleanup P ki ko cleanup).Cfg =>
          z.bind (compileWithCleanup P ki ko cleanup).step)^[n])
        (some ⟨some (some c.state), initialHeads, c.store⟩) =
          some ⟨some (some d.state), finalHeads, d.store⟩ := by
  induction hc with
  | refl c => exact fun initialHeads => ⟨initialHeads, rfl⟩
  | @cons n c d hd ht ih =>
    intro initialHeads
    obtain ⟨finalHeads, hfinal⟩ := ih (fun k => (c.store k).head?)
    refine ⟨finalHeads, ?_⟩
    rw [Function.iterate_succ_apply]
    erw [Option.bind_some, source_step_cfg P ki ko cleanup c hd initialHeads]
    exact hfinal

/-- The bounded-evaluation witness records exactly the source trace length. -/
theorem source_trace_steps (P : StackMachine K A Q) (ki ko : K) (cleanup : Statement K A Q)
    {n : ℕ} {c d : StackCfg K A Q} (hc : StackTrace P n c d) (initialHeads : Heads K A) :
    ∃ finalHeads : Heads K A, ∃ run : StateTransition.EvalsToInTime
      (compileWithCleanup P ki ko cleanup).step
      ⟨some (some c.state), initialHeads, c.store⟩
      (some ⟨some (some d.state), finalHeads, d.store⟩) n, run.steps = n := by
  obtain ⟨finalHeads, hfinal⟩ := source_trace_iterate P ki ko cleanup hc initialHeads
  exact ⟨finalHeads, ⟨⟨n, hfinal⟩, le_rfl⟩, rfl⟩

theorem source_trace (P : StackMachine K A Q) (ki ko : K) (cleanup : Statement K A Q)
    {n : ℕ} {c d : StackCfg K A Q} (hc : StackTrace P n c d) (initialHeads : Heads K A) :
    ∃ finalHeads : Heads K A, Nonempty (StateTransition.EvalsToInTime
      (compileWithCleanup P ki ko cleanup).step
      ⟨some (some c.state), initialHeads, c.store⟩
      (some ⟨some (some d.state), finalHeads, d.store⟩) n) := by
  exact match source_trace_steps P ki ko cleanup hc initialHeads with
    | ⟨finalHeads, run, _⟩ => ⟨finalHeads, ⟨run⟩⟩

end StackTM2Lift

end

/- Time -/
section

set_option autoImplicit false
open Turing CookPvsNP StateTransition StackTM2Bridge StackTM2Cleanup

namespace StackTM2Time
variable {K A Q : Type} [DecidableEq K] [Fintype K] [Fintype A] [Fintype Q] [Inhabited A]

lemma init_eq (P : StackMachine K A Q) (ki ko : K) (w : List A) :
    initList (machine P ki ko) w =
      ⟨some (some P.initial), (fun _ => none), (P.init ki w).store⟩ := by
  rfl


theorem trace_outputs (P : StackMachine K A Q) (ki ko : K) (w : List A)
    {n : Nat} {d : StackCfg K A Q}
    (ht : StackTrace P n (P.init ki w) d) (hd : P.done d.state = true) :
    Nonempty (TM2OutputsInTime (machine P ki ko) w (some (d.store ko))
      (2 * n + w.length + 2)) := by
  obtain ⟨h, hh⟩ := StackTM2Lift.source_trace_iterate P ki ko (cleanupStatement ko) ht (fun _ => none)
  have hr : EvalsToInTime (machine P ki ko).step (initList (machine P ki ko) w)
      (some ⟨some (some d.state), h, d.store⟩) n := by
    refine ⟨⟨n, ?_⟩, le_rfl⟩
    rw [init_eq]
    exact hh
  exact ⟨finish_run P ki ko w n d.state h d.store hd hr
    (fun k _ => StackTM2Trace.init_trace_store_length_le ht k)⟩


private def timeMono {C : Type} {f : C → Option C} {a : C} {b : Option C}
    {m n : Nat} (h : EvalsToInTime f a b m) (hmn : m ≤ n) : EvalsToInTime f a b n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hmn⟩

theorem program_outputs (p : StackProg K A) (ki ko : K) (w : List A)
    {t : K → List A} {n : Nat} (hp : p.Exec ((p.machine.init ki w).store) t n) :
    Nonempty (TM2OutputsInTime (machine p.machine ki ko) w (some (t ko))
      (2 * n + w.length + 2)) := by
  obtain ⟨q, hq, ht⟩ := StackTM2Trace.Exec_trace hp
  exact trace_outputs p.machine ki ko w ht hq

noncomputable def programPolytime {α β : Type} (ea : α → List A) (eb : β → List A)
    (f : α → β) (p : StackProg K A) (ki ko : K) (b : Polynomial ℕ)
    (hp : ∀ a, ∃ t n, p.Exec ((p.machine.init ki (ea a)).store) t n ∧
      t ko = eb (f a) ∧ n ≤ b.eval (ea a).length) :
    TM2ComputableInPolyTime ea eb f where
  tm := machine p.machine ki ko
  inputAlphabet := Equiv.refl A
  outputAlphabet := Equiv.refl A
  time := 2 * b + Polynomial.X + 2
  outputsFun a := by
    apply Classical.choice
    obtain ⟨t, n, hrun, hout, hbound⟩ := hp a
    obtain ⟨run⟩ := program_outputs p ki ko (ea a) hrun
    rw [hout] at run
    change Nonempty (TM2OutputsInTime (machine p.machine ki ko) (List.map id (ea a))
      (some (List.map id (eb (f a)))) ((2 * b + Polynomial.X + 2).eval (ea a).length))
    simp only [List.map_id_fun]
    refine ⟨timeMono run ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    omega

end StackTM2Time

end

/- InstanceInputMachines -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines

open CookPvsNP OAI.PerfectCompleteness

/-- The adjacency matrix in the exact order used by the LabelCover encoder. -/
def adjacencyBits (P : LabelCover) : List Bool :=
  (List.finRange P.nL).flatMap fun u =>
    (List.finRange P.nR).map fun v => decide ((u, v) ∈ P.edges)

private def projectionRow (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR) : List ℕ :=
  (List.finRange P.sizeL).map fun a => (P.proj u v a : ℕ)

/-- The dense projection table, including the entries at nonedges. -/
def projectionWords (P : LabelCover) : List ℕ :=
  (List.finRange P.nL).flatMap fun u =>
    (List.finRange P.nR).flatMap (fun v => projectionRow P u v)

theorem labelCover_input_layout (P : LabelCover) :
    encodeLabelCover P =
      ([P.nL, P.nR, P.sizeL, P.sizeR].flatMap (unary true false)) ++
        adjacencyBits P ++ (projectionWords P).flatMap (unary true false) := by
  simp [encodeLabelCover, adjacencyBits, projectionWords, projectionRow, List.flatMap_map,
    List.flatMap_assoc, unary, unaryCode, List.append_assoc]

theorem labelCover_header_exec (P : LabelCover) :
    (readFour true).Exec ![encodeLabelCover P, [], [], [], []]
      ![adjacencyBits P ++ (projectionWords P).flatMap (unary true false),
        List.replicate P.nL true, List.replicate P.nR true,
        List.replicate P.sizeL true, List.replicate P.sizeR true]
      (3 * (P.nL + P.nR + P.sizeL + P.sizeR) + 15) := by
  simpa only [labelCover_input_layout, List.append_assoc] using
    readFour_exec true false (by decide) P.nL P.nR P.sizeL P.sizeR
      (adjacencyBits P ++ (projectionWords P).flatMap (unary true false))

open OAI.UniqueGamesTheorem.Foundations.Complexity

private theorem encodeWords_unary (ns : List ℕ) :
    encodeWords ns = ns.flatMap (unary true false) := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [encodeWords, encodeWord, unary, ih]

theorem gameBits_input_layout {q : ℕ} (G : Instance q) :
    Encoding.gameBits G =
      ([G.leftVertices, G.rightVertices, q, G.edges.length].flatMap (unary true false)) ++
        (G.edges.flatMap Encoding.edgeWords).flatMap (unary true false) := by
  simp only [Encoding.gameBits, Encoding.gameWords, encodeWords_unary, List.flatMap_append]

theorem twoToOne_header_exec {q : ℕ} (G : Instance q) :
    (readFour true).Exec ![Encoding.gameBits G, [], [], [], []]
      ![(G.edges.flatMap Encoding.edgeWords).flatMap (unary true false),
        List.replicate G.leftVertices true, List.replicate G.rightVertices true,
        List.replicate q true, List.replicate G.edges.length true]
      (3 * (G.leftVertices + G.rightVertices + q + G.edges.length) + 15) := by
  simpa only [gameBits_input_layout] using
    readFour_exec true false (by decide) G.leftVertices G.rightVertices q G.edges.length
      ((G.edges.flatMap Encoding.edgeWords).flatMap (unary true false))


section RowMajor

variable {α β : Type}

private theorem flatMap_length_rows (rows : List α) (row : α → List β) (width : ℕ)
    (hlen : ∀ a ∈ rows, (row a).length = width) :
    (rows.flatMap row).length = rows.length * width := by
  rw [List.length_flatMap, List.map_eq_replicate_iff.mpr hlen, List.sum_replicate]
  exact Nat.nsmul_eq_mul _ _

private theorem rowIndex_lt {i n j width : ℕ} (hi : i < n) (hj : j < width) :
    i * width + j < n * width := by
  have h := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at h
  omega

private theorem flatMap_get_rows (rows : List α) (row : α → List β) (width : ℕ)
    (hlen : ∀ a ∈ rows, (row a).length = width)
    {i j : ℕ} (hi : i < rows.length) (hj : j < width) :
    (rows.flatMap row)[i * width + j]'(by
      rw [flatMap_length_rows rows row width hlen]
      exact rowIndex_lt hi hj) =
    (row rows[i])[j]'(by rw [hlen _ (List.getElem_mem hi)]; exact hj) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons a rows ih =>
      cases i with
      | zero =>
          simpa only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
            using (List.getElem_append_left (as := row a) (bs := rows.flatMap row)
              (by rw [hlen _ (by simp)]; exact hj : j < (row a).length))
      | succ i =>
          simp only [List.flatMap_cons, List.getElem_cons_succ]
          rw [List.getElem_append_right
            (by rw [hlen _ (by simp), Nat.succ_mul]; omega)]
          have hoff : (i + 1) * width + j - (row a).length = i * width + j := by
            rw [hlen _ (by simp), Nat.succ_mul]
            omega
          simpa only [hoff] using ih (fun a ha => hlen a (List.mem_cons_of_mem _ ha))
            (by simpa using hi : i < rows.length)


private theorem projectionRow_length (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR) :
    (projectionRow P u v).length = P.sizeL := by simp [projectionRow]

private theorem projectionRows_length (P : LabelCover) (u : Fin P.nL) :
    ((List.finRange P.nR).flatMap (projectionRow P u)).length = P.nR * P.sizeL := by
  simpa only [List.length_finRange] using flatMap_length_rows (List.finRange P.nR)
    (projectionRow P u) P.sizeL (fun v _ => projectionRow_length P u v)

theorem projectionWords_length (P : LabelCover) :
    (projectionWords P).length = P.nL * (P.nR * P.sizeL) := by
  simpa only [projectionWords, List.length_finRange] using
    flatMap_length_rows (List.finRange P.nL)
      (fun u => (List.finRange P.nR).flatMap (projectionRow P u)) (P.nR * P.sizeL)
      (fun u _ => projectionRows_length P u)

theorem projectionWords_get (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR) (a : Fin P.sizeL) :
    (projectionWords P)[u.val * (P.nR * P.sizeL) + (v.val * P.sizeL + a.val)]'(by
      rw [projectionWords_length]
      exact rowIndex_lt u.isLt (rowIndex_lt v.isLt a.isLt)) =
    (P.proj u v a : ℕ) := by
  have h := flatMap_get_rows (List.finRange P.nL)
    (fun u => (List.finRange P.nR).flatMap (projectionRow P u)) (P.nR * P.sizeL)
    (fun u _ => projectionRows_length P u) (i := u.val) (j := v.val * P.sizeL + a.val)
    (by simp) (rowIndex_lt v.isLt a.isLt)
  have h' := flatMap_get_rows (List.finRange P.nR) (projectionRow P u) P.sizeL
    (fun v _ => projectionRow_length P u v) (i := v.val) (j := a.val) (by simp)
    a.isLt
  calc
    _ = ((List.finRange P.nR).flatMap (projectionRow P u))[v.val * P.sizeL + a.val]'(by
      rw [projectionRows_length]
      exact rowIndex_lt v.isLt a.isLt) := by simpa [projectionWords] using h
    _ = (projectionRow P u v)[a.val]'(by simp [projectionRow]) := by simpa using h'
    _ = _ := by simp [projectionRow]

private theorem edgeWords_length {l r q : ℕ} (e : Edge l r q) :
    (Encoding.edgeWords e).length = 2 + 2 * q := by
  simp [Encoding.edgeWords, Encoding.tableWords]
  omega

theorem twoToOne_payload_length {q : ℕ} (G : Instance q) :
    (G.edges.flatMap Encoding.edgeWords).length = G.edges.length * (2 + 2*q) :=
  flatMap_length_rows _ _ _ (fun e _ => edgeWords_length e)

theorem twoToOne_projection_get {q : ℕ} (G : Instance q) (e : Fin G.edges.length)
    (a : Fin (2*q)) :
    (G.edges.flatMap Encoding.edgeWords)[e.val * (2 + 2*q) + (2 + a.val)]'(by
      rw [twoToOne_payload_length]
      exact rowIndex_lt e.isLt (by have := a.isLt; omega)) =
    ((G.edges.get e).projection.images[a] : ℕ) := by
  have h := flatMap_get_rows G.edges Encoding.edgeWords (2 + 2*q)
    (fun e _ => edgeWords_length e) (i := e.val) (j := 2 + a.val) e.isLt
    (by have := a.isLt; omega)
  refine h.trans ?_
  simp [Encoding.edgeWords, Encoding.tableWords, Nat.add_comm]


/-- Read an exact LabelCover projection entry once the adjacency bits have been split off. -/
theorem labelCover_projection_exec (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR)
    (a : Fin P.sizeL) (out : List Bool) :
    let w := (projectionWords P).flatMap (unary true false)
    let i := u.val * (P.nR * P.sizeL) + (v.val * P.sizeL + a.val)
    let ix := List.replicate i true
    ∃ t, (lookupField true).Exec (lookupStore w ix out)
      (lookupStore w ix (List.replicate (P.proj u v a).val true ++ out)) t ∧
      t ≤ 10 * w.length + 10 * i + 15 := by
  dsimp only
  let i := u.val * (P.nR * P.sizeL) + (v.val * P.sizeL + a.val)
  have hIdx : i < (projectionWords P).length := by
    rw [projectionWords_length]
    exact rowIndex_lt u.isLt (rowIndex_lt v.isLt a.isLt)
  obtain ⟨t, ht, hb⟩ := lookupField_at true false (projectionWords P)
    (List.replicate i true) out (by decide) (by simpa using hIdx)
  exact ⟨t, by simpa only [List.length_replicate, projectionWords_get, i] using ht,
    by simpa only [List.length_replicate] using hb⟩

/-- Read the projection at a specified edge ordinal and left label in the 2-to-1 input. -/
theorem twoToOne_projection_exec {q : ℕ} (G : Instance q) (e : Fin G.edges.length)
    (a : Fin (2*q)) (out : List Bool) :
    let w := (G.edges.flatMap Encoding.edgeWords).flatMap (unary true false)
    let i := e.val * (2 + 2*q) + (2 + a.val)
    let ix := List.replicate i true
    ∃ t, (lookupField true).Exec (lookupStore w ix out)
      (lookupStore w ix (List.replicate ((G.edges.get e).projection.images[a]).val true ++ out)) t ∧
      t ≤ 10 * w.length + 10 * i + 15 := by
  dsimp only
  let i := e.val * (2 + 2*q) + (2 + a.val)
  have hIdx : i < (G.edges.flatMap Encoding.edgeWords).length := by
    rw [twoToOne_payload_length]
    exact rowIndex_lt e.isLt (by have := a.isLt; omega)
  obtain ⟨t, ht, hb⟩ := lookupField_at true false (G.edges.flatMap Encoding.edgeWords)
    (List.replicate i true) out (by decide) (by simpa using hIdx)
  exact ⟨t, by simpa only [List.length_replicate, twoToOne_projection_get, i] using ht,
    by simpa only [List.length_replicate] using hb⟩

end RowMajor

theorem adjacencyBits_length (P : LabelCover) : (adjacencyBits P).length = P.nL * P.nR := by
  simpa only [adjacencyBits, List.length_finRange] using flatMap_length_rows (List.finRange P.nL)
    (fun u => (List.finRange P.nR).map fun v => decide ((u,v) ∈ P.edges)) P.nR
    (fun _ _ => by simp)

theorem adjacencyBits_get (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR) :
    (adjacencyBits P)[u.val * P.nR + v.val]'(by
      rw [adjacencyBits_length]
      exact rowIndex_lt u.isLt v.isLt) = decide ((u,v) ∈ P.edges) := by
  simpa [adjacencyBits] using flatMap_get_rows (List.finRange P.nL)
    (fun u => (List.finRange P.nR).map fun v => decide ((u,v) ∈ P.edges)) P.nR
    (fun _ _ => by simp) (i := u.val) (j := v.val) (by simp) v.isLt

theorem adjacencyBits_any (P : LabelCover) :
    (adjacencyBits P).any id = decide P.edges.Nonempty := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, id_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp hb
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hu
    exact ⟨(u,v), of_decide_eq_true hv⟩
  · rintro ⟨⟨u,v⟩, h⟩
    refine ⟨true, ?_, rfl⟩
    exact List.mem_flatMap.mpr
      ⟨u, by simp, List.mem_map.mpr ⟨v, by simp, decide_eq_true h⟩⟩

theorem detectsEdge_exec (P : LabelCover) (out : List Bool) :
    ∃ t, anyTrue.Exec ![adjacencyBits P, out, [], []]
      ![adjacencyBits P, decide P.edges.Nonempty :: out, [], []] t ∧
      t ≤ 9 * (P.nL * P.nR) + 9 := by
  simpa only [adjacencyBits_any, adjacencyBits_length] using anyTrue_exec (adjacencyBits P) out

private theorem sideOffset_lt (q : ℕ) (right : Bool) : right.toNat < 2 + 2*q := by
  cases right <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem twoToOne_endpoint_get {q : ℕ} (G : Instance q) (e : Fin G.edges.length)
    (right : Bool) :
    (G.edges.flatMap Encoding.edgeWords)[e.val * (2 + 2*q) + right.toNat]'(by
      rw [twoToOne_payload_length]
      exact rowIndex_lt e.isLt (sideOffset_lt q right)) =
    if right then (G.edges.get e).right.val else (G.edges.get e).left.val := by
  have h := flatMap_get_rows G.edges Encoding.edgeWords (2 + 2*q)
    (fun e _ => edgeWords_length e) (i := e.val) (j := right.toNat)
    e.isLt (sideOffset_lt q right)
  refine h.trans ?_
  cases right <;> rfl

theorem twoToOne_endpoint_exec {q : ℕ} (G : Instance q) (e : Fin G.edges.length)
    (right : Bool) (out : List Bool) :
    let w := (G.edges.flatMap Encoding.edgeWords).flatMap (unary true false)
    let i := e.val * (2 + 2*q) + right.toNat
    let ix := List.replicate i true
    let v := if right then (G.edges.get e).right.val else (G.edges.get e).left.val
    ∃ t, (lookupField true).Exec (lookupStore w ix out)
      (lookupStore w ix (List.replicate v true ++ out)) t ∧
      t ≤ 10 * w.length + 10 * i + 15 := by
  dsimp only
  let i := e.val * (2 + 2*q) + right.toNat
  have hIdx : i < (G.edges.flatMap Encoding.edgeWords).length := by
    rw [twoToOne_payload_length]
    exact rowIndex_lt e.isLt (sideOffset_lt q right)
  obtain ⟨t, ht, hb⟩ := lookupField_at true false (G.edges.flatMap Encoding.edgeWords)
    (List.replicate i true) out (by decide) (by simpa using hIdx)
  exact ⟨t, by simpa only [List.length_replicate, twoToOne_endpoint_get, i] using ht,
    by simpa only [List.length_replicate] using hb⟩

def projectionPayload (P : LabelCover) : List Bool := (projectionWords P).flatMap (unary true false)

private def headerPorts : Fin 5 ↪ Fin 10 := ⟨![0,1,2,3,4], by decide⟩
private def multPorts : Fin 5 ↪ Fin 10 := ⟨![1,2,5,7,8], by decide⟩
private def splitPorts : Fin 6 ↪ Fin 10 := ⟨![0,5,6,7,8,9], by decide⟩

private theorem inputLength_lower (P : LabelCover) :
    P.nL + P.nR + P.sizeL + P.sizeR + P.nL * P.nR ≤ (encodeLabelCover P).length := by
  rw [labelCover_input_layout P]
  simp [unary, adjacencyBits_length]
  omega

/-- Prepare the four counters, the adjacency length, and separate adjacency and projection tapes. -/
noncomputable def loadLabelCover : StackProg (Fin 10) Bool :=
  .seq (onPorts headerPorts (readFour true))
    (.seq (onPorts multPorts multiply) (onPorts splitPorts splitPrefix))

private def headerStore (P : LabelCover) : Fin 10 → List Bool :=
  ![adjacencyBits P ++ projectionPayload P,
    List.replicate P.nL true, List.replicate P.nR true,
    List.replicate P.sizeL true, List.replicate P.sizeR true,
    [], [], [], [], []]

private def countedStore (P : LabelCover) : Fin 10 → List Bool :=
  Function.update (headerStore P) 5 (List.replicate (P.nL * P.nR) true)

def loadedStore (P : LabelCover) : Fin 10 → List Bool :=
  Function.update (Function.update (countedStore P) 0 (projectionPayload P)) 6 (adjacencyBits P)

theorem loadLabelCover_exec (P : LabelCover) :
    ∃ t, loadLabelCover.Exec ((loadLabelCover.machine.init 0 (encodeLabelCover P)).store)
      (loadedStore P) t ∧ t ≤ 18 * (encodeLabelCover P).length + 29 := by
  let base := (loadLabelCover.machine.init 0 (encodeLabelCover P)).store
  let cnt := List.replicate (P.nL * P.nR) true
  let adj := adjacencyBits P
  let table := projectionPayload P
  let s1 := headerStore P
  let s2 := countedStore P
  have h1 : (onPorts headerPorts (readFour true)).Exec base s1
      (3 * (P.nL + P.nR + P.sizeL + P.sizeR) + 15) := by
    refine onPorts_exec headerPorts (labelCover_header_exec P) ?_ ?_ ?_
    · intro k
      fin_cases k <;> simp [base, StackMachine.init, headerPorts]
    · intro k
      fin_cases k <;> rfl
    · intro l h
      fin_cases l <;>
        first | exact (h 0 rfl).elim | exact (h 1 rfl).elim |
          exact (h 2 rfl).elim | exact (h 3 rfl).elim | exact (h 4 rfl).elim |
          simp [base, StackMachine.init, s1, headerStore]
  have h2 : (onPorts multPorts multiply).Exec s1 s2
      ((6 * P.nL + 13) * P.nR + 5) := by
    refine onPorts_exec multPorts (multiply_exec true P.nL P.nR []) ?_ ?_ ?_
    · intro k
      fin_cases k <;> rfl
    · intro k
      fin_cases k <;> simp [s2, countedStore, headerStore, multPorts]
    · intro l h
      have hl : l ≠ 5 := fun he => h 2 he.symm
      simp [s2, s1, countedStore, hl]
  have hc : cnt.length = adj.length := by simp [cnt, adj, adjacencyBits_length]
  have h3 : (onPorts splitPorts splitPrefix).Exec s2 (loadedStore P)
      (12 * adj.length + 7) := by
    refine onPorts_exec splitPorts (splitPrefix_exec adj table cnt [] hc) ?_ ?_ ?_
    · intro k
      fin_cases k <;> rfl
    · intro k
      fin_cases k
      · rfl
      · rfl
      · change adj = adj ++ []
        simp
      · rfl
      · rfl
      · rfl
    · intro l h
      have h0 : l ≠ 0 := fun he => h 0 he.symm
      have h6 : l ≠ 6 := fun he => h 2 he.symm
      simp [s2, loadedStore, h0, h6]
  refine ⟨_, h1.seq (h2.seq h3), ?_⟩
  have hlen := inputLength_lower P
  simp only [adj, adjacencyBits_length, Nat.add_mul, Nat.mul_assoc]
  omega

/-- The projection payload is computed from the exact published binary encoding. -/
noncomputable def projectionPayload_polytime :
    Turing.TM2ComputableInPolyTime encodeLabelCover id projectionPayload :=
  StackTM2Time.programPolytime encodeLabelCover id projectionPayload loadLabelCover 0 0
    (18 * Polynomial.X + 29) (fun P => by
      obtain ⟨t, ht, hb⟩ := loadLabelCover_exec P
      refine ⟨loadedStore P, t, ht, rfl, ?_⟩
      simpa using hb)


end FourToOneGames.WordMachines

end

/- Alphabet -/
section

set_option autoImplicit false

open CookPvsNP

namespace StackProgAlphabet

variable {K A B : Type}

/-- Pointwise alphabet embedding of every stack word. -/
def mapStore (enc : A → B) (s : K → List A) : K → List B :=
  fun k => (s k).map enc

/-- Decode the saved top of each target stack. -/
def decodeHeads (dec : B → A) (h : K → Option B) : K → Option A :=
  fun k => (h k).map dec

/-- Push payloads are encoded; keep and pop are unchanged. -/
def mapAction (enc : A → B) : StackAct A → StackAct B
  | .keep => .keep
  | .push a => .push (enc a)
  | .pop => .pop

/-- Translate an atomic action by decoding the captured heads. -/
def mapAct (enc : A → B) (dec : B → A)
    (f : (K → Option A) → K → StackAct A) : (K → Option B) → K → StackAct B :=
  fun h k => mapAction enc (f (decodeHeads dec h) k)

/-- Translate finite source syntax without changing its control structure. -/
def mapProg (enc : A → B) (dec : B → A) : StackProg K A → StackProg K B
  | .act f => .act (mapAct enc dec f)
  | .seq p q => .seq (mapProg enc dec p) (mapProg enc dec q)
  | .branch test p q => .branch (fun h => test (decodeHeads dec h))
      (mapProg enc dec p) (mapProg enc dec q)
  | .loop test p => .loop (fun h => test (decodeHeads dec h)) (mapProg enc dec p)

theorem decodeHeads_mapStore (enc : A → B) (dec : B → A)
    (hinv : Function.LeftInverse dec enc) (s : K → List A) :
    decodeHeads dec (fun k => (mapStore enc s k).head?) = fun k => (s k).head? := by
  funext k
  cases hs : s k with
  | nil => simp [decodeHeads, mapStore, hs]
  | cons a as => simpa [decodeHeads, mapStore, hs] using congrArg some (hinv a)

theorem mapAction_apply (enc : A → B) (a : StackAct A) (s : List A) :
    (mapAction enc a).apply (s.map enc) = (a.apply s).map enc := by
  cases a <;> simp [mapAction, StackAct.apply]

theorem mapAct_applyAct (enc : A → B) (dec : B → A)
    (hinv : Function.LeftInverse dec enc)
    (f : (K → Option A) → K → StackAct A) (s : K → List A) :
    StackProg.applyAct (mapAct enc dec f) (mapStore enc s) =
      mapStore enc (StackProg.applyAct f s) := by
  funext k
  change (mapAction enc (f (decodeHeads dec (fun j => (mapStore enc s j).head?)) k)).apply
    ((s k).map enc) = ((f (fun j => (s j).head?) k).apply (s k)).map enc
  rw [decodeHeads_mapStore enc dec hinv]
  exact mapAction_apply enc _ _

/-- Alphabet translation preserves every valid execution with its exact step count. -/
theorem mapProg_exec (enc : A → B) (dec : B → A)
    (hinv : Function.LeftInverse dec enc) {p : StackProg K A}
    {s t : K → List A} {n : ℕ} (h : p.Exec s t n) :
    (mapProg enc dec p).Exec (mapStore enc s) (mapStore enc t) n := by
  induction h with
  | act f s =>
    simpa only [mapProg, mapAct_applyAct enc dec hinv] using
      (StackProg.Exec.act (mapAct enc dec f) (mapStore enc s))
  | seq hp hq ihp ihq =>
    exact StackProg.Exec.seq ihp ihq
  | branchTrue htest hp ih =>
    apply StackProg.Exec.branchTrue ?_ ih
    simpa only [decodeHeads_mapStore enc dec hinv] using htest
  | branchFalse htest hq ih =>
    apply StackProg.Exec.branchFalse ?_ ih
    simpa only [decodeHeads_mapStore enc dec hinv] using htest
  | loopFalse htest =>
    apply StackProg.Exec.loopFalse
    simpa only [decodeHeads_mapStore enc dec hinv] using htest
  | loopTrue htest hp hl ihp ihl =>
    apply StackProg.Exec.loopTrue ?_ ihp ihl
    simpa only [decodeHeads_mapStore enc dec hinv] using htest

end StackProgAlphabet

end

/- NativeInput -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open ProjSchedTW.Complexity
open CLRS.Chapter34.Turing.PolyBuilder
open WordMachines CookPvsNP

def nativeBit (b : Bool) : BSym := if b then .one else .zero

def fromNativeBit (a : BSym) : Bool := decide (a = .one)

private theorem fromNative_native : Function.LeftInverse fromNativeBit nativeBit := by
  intro b
  cases b <;> rfl

private def bitSpec : StatefulFlatMapSpec Unit Bool BSym where
  initial := ()
  action _ b := ([nativeBit b], ())
  finish _ := []

private theorem bitSpec_correct (w : List Bool) :
    rewriteStatefulFlatMap bitSpec w = w.map nativeBit := by
  induction w with
  | nil => rfl
  | cons b w ih => exact congrArg (nativeBit b :: ·) ih

/-- Convert Boolean input to the native arithmetic and binary-writer alphabet. -/
noncomputable def nativeBits_polytime :
    Turing.TM2ComputableInPolyTime id id (List.map nativeBit) := by
  simpa only [funext bitSpec_correct] using statefulFlatMap_computableInPolyTime bitSpec

/-- Run the checked LabelCover input loader over the native arithmetic alphabet. -/
noncomputable def nativeLoad : StackProg (Fin 10) BSym :=
  StackProgAlphabet.mapProg nativeBit fromNativeBit loadLabelCover

theorem nativeLoad_exec (P : LabelCover) :
    ∃ t, nativeLoad.Exec ((nativeLoad.machine.init 0 ((encodeLabelCover P).map nativeBit)).store)
      (StackProgAlphabet.mapStore nativeBit (loadedStore P)) t ∧
      t ≤ 18 * (encodeLabelCover P).length + 29 := by
  obtain ⟨t, ht, hb⟩ := loadLabelCover_exec P
  have hr := StackProgAlphabet.mapProg_exec nativeBit fromNativeBit fromNative_native ht
  refine ⟨t, ?_, hb⟩
  have hstate : (nativeLoad.machine.init 0 ((encodeLabelCover P).map nativeBit)).store =
      StackProgAlphabet.mapStore nativeBit ((loadLabelCover.machine.init 0 (encodeLabelCover P)).store) := by
    funext k
    by_cases hk : k = 0 <;> simp [StackProgAlphabet.mapStore, StackMachine.init, hk]
  rw [hstate]
  exact hr

end FourToOneGames.SATMachine

end

/- UnaryDivision -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.UnaryDivision

open CookPvsNP

variable {A : Type}

def store (token : A) (n d fuel q r : ℕ) : Fin 6 → List A :=
  ![List.replicate n token, List.replicate d token, List.replicate fuel token,
    List.replicate q token, List.replicate r token, []]

private def keep : StackProg (Fin 6) A := .act (fun _ _ => .keep)

private def tickAct (token : A) (_ : Fin 6 → Option A) (k : Fin 6) : StackAct A :=
  if k = 0 ∨ k = 2 then .pop else if k = 4 then .push token else .keep

private def wrap (token : A) : StackProg (Fin 6) A :=
  .seq (pushProg 3 token) (.seq (clearProg 4) (copyProg 1 2 5))

private def checkWrap (token : A) : StackProg (Fin 6) A :=
  .branch (fun h => (h 2).isNone) (wrap token) keep

private def scan (token : A) : StackProg (Fin 6) A :=
  .loop (fun h => (h 0).isSome) (.seq (.act (tickAct token)) (checkWrap token))

/-- Divide one unary length by a positive unary divisor, using a refillable countdown. -/
def divide (token : A) : StackProg (Fin 6) A :=
  .seq (copyProg 1 2 5) (.seq (scan token) (clearProg 2))

private theorem tick_exec (token : A) (n d f q r : ℕ) :
    (StackProg.act (tickAct token)).Exec (store token (n+1) d (f+1) q r)
      (store token n d f q (r+1)) 1 := by
  convert StackProg.Exec.act (tickAct token) (store token (n+1) d (f+1) q r) using 1
  exact funext (fun k => by fin_cases k <;>
    simp [store, StackProg.applyAct, tickAct, StackAct.apply, List.replicate_succ])

private theorem refill_exec (token : A) (n d q r : ℕ) :
    (copyProg (1 : Fin 6) 2 5).Exec (store token n d 0 q r)
      (store token n d d q r) (6*d+3) := by
  convert stack_copy (1 : Fin 6) 2 5 (by decide) (by decide) (by decide)
    (store token n d 0 q r) rfl using 1 <;>
    first | rfl | exact funext (fun k => by fin_cases k <;> simp [store]) |
      solve | simp [store]

private theorem wrap_exec (token : A) (n d q r : ℕ) :
    (wrap token).Exec (store token n d 0 q r) (store token n d d (q+1) 0)
      (6*d+3*r+7) := by
  have hp : (pushProg (3 : Fin 6) token).Exec (store token n d 0 q r)
      (store token n d 0 (q+1) r) 1 := by
    unfold pushProg
    convert StackProg.Exec.act _ (store token n d 0 q r) using 1
    exact funext (fun k => by fin_cases k <;>
      simp [store, StackProg.applyAct, StackAct.apply, List.replicate_succ])
  have hc : (clearProg (4 : Fin 6)).Exec (store token n d 0 (q+1) r)
      (store token n d 0 (q+1) 0) (3*r+1) := by
    convert clear_exec (4 : Fin 6) (store token n d 0 (q+1) r) using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> simp [store]) |
        solve | simp [store]
  convert hp.seq (hc.seq (refill_exec token n d (q+1) 0)) using 1 <;> first | rfl | omega

private theorem keep_exec (s : Fin 6 → List A) : keep.Exec s s 1 := by
  exact StackProg.Exec.act _ s

private theorem scan_exec (token : A) (n d q r : ℕ) (hr : r < d) :
    ∃ Q R t, (scan token).Exec (store token n d (d-r) q r)
      (store token 0 d (d-R) Q R) t ∧
      R < d ∧ Q*d+R = q*d+r+n ∧ t ≤ 12*(d+1)*n+1 := by
  induction n generalizing q r with
  | zero =>
      exact ⟨q, r, 1, StackProg.Exec.loopFalse rfl, hr, by omega, by simp⟩
  | succ n ih =>
      let f := d - (r+1)
      have hf : f+1 = d-r := by dsimp [f]; omega
      have ha : (StackProg.act (tickAct token)).Exec
          (store token (n+1) d (d-r) q r) (store token n d f q (r+1)) 1 := by
        simpa only [hf] using tick_exec token n d f q r
      have hg : ((store token (n+1) d (d-r) q r 0).head?).isSome = true := rfl
      by_cases h : r+1 < d
      · have hfpos : 0 < f := by dsimp [f]; omega
        have htest : ((store token n d f q (r+1) 2).head?).isNone = false := by
          obtain ⟨g, hg⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
          rw [hg]
          rfl
        have hb : (checkWrap token).Exec (store token n d f q (r+1))
            (store token n d f q (r+1)) 2 := StackProg.Exec.branchFalse htest (keep_exec _)
        obtain ⟨Q, R, t, ht, hR, hv, hbnd⟩ := ih q (r+1) h
        refine ⟨Q, R, _, StackProg.Exec.loopTrue hg (ha.seq hb) ht, hR, by omega, ?_⟩
        simp only [Nat.mul_succ] at hbnd ⊢
        omega
      · have hfull : r+1 = d := by omega
        have hfzero : f = 0 := by simp [f, hfull]
        have htest : ((store token n d f q (r+1) 2).head?).isNone = true := by
          rw [hfzero]
          rfl
        have hw : (wrap token).Exec (store token n d f q (r+1))
            (store token n d d (q+1) 0) (6*d+3*(r+1)+7) := by
          rw [hfzero]
          exact wrap_exec token n d q (r+1)
        have hb := StackProg.Exec.branchTrue (q := keep)
          (test := fun h => (h (2 : Fin 6)).isNone) htest hw
        obtain ⟨Q, R, t, ht, hR, hv, hbnd⟩ := ih (q+1) 0 (by omega)
        simp only [Nat.sub_zero] at ht
        refine ⟨Q, R, _, StackProg.Exec.loopTrue hg (ha.seq hb) ht, hR, ?_, ?_⟩
        · rw [Nat.succ_mul] at hv
          omega
        · simp only [Nat.mul_succ] at hbnd ⊢
          omega

theorem divide_exec (token : A) (n d : ℕ) (hd : 0 < d) :
    ∃ t, (divide token).Exec (store token n d 0 0 0) (store token 0 d 0 (n/d) (n%d)) t ∧
      t ≤ 12*(d+1)*(n+1)+8 := by
  obtain ⟨Q, R, t, ht, hR, hv, hb⟩ := scan_exec token n d 0 0 hd
  simp only [Nat.sub_zero] at ht
  simp only [Nat.zero_mul, Nat.zero_add] at hv
  have hmod : n%d = R := by
    rw [← hv, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hR]
  have hdiv : n/d = Q := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.succ_mul]
      omega
  have hc : (clearProg (2 : Fin 6)).Exec (store token 0 d (d-R) Q R)
      (store token 0 d 0 Q R) (3*(d-R)+1) := by
    convert clear_exec (2 : Fin 6) (store token 0 d (d-R) Q R) using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> simp [store]) |
        solve | simp [store]
  have he := (refill_exec token n d 0 0).seq (ht.seq hc)
  rw [← hdiv, ← hmod] at he
  refine ⟨_, he, ?_⟩
  simp only [Nat.mul_succ] at hb ⊢
  omega

private def trialPorts : Fin 6 ↪ Fin 8 := ⟨![2,1,3,4,5,6], by decide⟩

private def trialState (n d input quotient remainder : ℕ) (out : List Bool) :
    Fin 8 → List Bool :=
  ![List.replicate n true, List.replicate d true, List.replicate input true, [],
    List.replicate quotient true, List.replicate remainder true, [], out]

def trialStore (n d : ℕ) (out : List Bool) : Fin 8 → List Bool := trialState n d 0 0 0 out

private def emitDivides (h : Fin 8 → Option Bool) (k : Fin 8) : StackAct Bool :=
  if k = 7 then .push (h 5).isNone else .keep

/-- Test a positive divisor while retaining both unary arguments for the next trial. -/
noncomputable def trialDivisor : StackProg (Fin 8) Bool :=
  .seq (copyProg 0 2 6) (.seq (onPorts trialPorts (divide true)) (.seq (.act emitDivides)
    (.seq (clearProg 4) (clearProg 5))))

theorem trialDivisor_exec (n d : ℕ) (hd : 0 < d) (out : List Bool) :
    ∃ t, trialDivisor.Exec (trialStore n d out)
      (trialStore n d (decide (d ∣ n) :: out)) t ∧
      t ≤ 12*(d+1)*(n+1)+9*n+3*d+18 := by
  let q := n/d
  let r := n%d
  let emit := decide (d ∣ n)
  let s0 := trialStore n d out
  let s1 := trialState n d n 0 0 out
  let s2 := trialState n d 0 q r out
  let s3 := trialState n d 0 q r (emit :: out)
  let s4 := trialState n d 0 0 r (emit :: out)
  let s5 := trialStore n d (emit :: out)
  have hc : (copyProg (0 : Fin 8) 2 6).Exec s0 s1 (6*n+3) := by
    convert stack_copy (0 : Fin 8) 2 6 (by decide) (by decide) (by decide) s0 rfl using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;>
        simp [s0, s1, trialStore, trialState]) |
        solve | simp [s0, trialStore, trialState]
  obtain ⟨v, hv, hb⟩ := divide_exec true n d hd
  have hcalc : (onPorts trialPorts (divide true)).Exec s1 s2 v := by
    refine onPorts_exec trialPorts hv ?_ ?_ ?_
    · intro k
      fin_cases k <;> rfl
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      fin_cases k
      · rfl
      · rfl
      · exact (hk 0 rfl).elim
      · rfl
      · exact (hk 3 rfl).elim
      · exact (hk 4 rfl).elim
      · rfl
      · rfl
  have hflag : ((List.replicate r true).head?).isNone = emit := by
    simp [emit, r, Nat.dvd_iff_mod_eq_zero]
    cases n % d <;> rfl
  have he : (StackProg.act emitDivides).Exec s2 s3 1 := by
    convert StackProg.Exec.act emitDivides s2 using 1
    exact funext (fun k => by fin_cases k <;>
      simp [s2, s3, trialState, StackProg.applyAct, emitDivides, StackAct.apply, hflag])
  have hq : (clearProg (4 : Fin 8)).Exec s3 s4 (3*q+1) := by
    convert clear_exec (4 : Fin 8) s3 using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl) |
        solve | simp [s3, trialState]
  have hr : (clearProg (5 : Fin 8)).Exec s4 s5 (3*r+1) := by
    convert clear_exec (5 : Fin 8) s4 using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl) |
        solve | simp [s4, trialState]
  refine ⟨_, hc.seq (hcalc.seq (he.seq (hq.seq hr))), ?_⟩
  have hqle : q ≤ n := Nat.div_le_self _ _
  have hrlt : r < d := Nat.mod_lt _ hd
  omega

end FourToOneGames.WordMachines.UnaryDivision

end

/- LiftRadix -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.Radix

open CookPvsNP

/-- Leave the quotient on the original input tape and write the remainder to its digit tape. -/
def extract : StackProg (Fin 6) Bool :=
  .seq (UnaryDivision.divide true) (transferProg 3 (fun k => decide (k = 0)))

private def state (n p r : ℕ) : Fin 6 → List Bool :=
  ![List.replicate n true, List.replicate p true, [], [], List.replicate r true, []]

def extractBound (n p : ℕ) : ℕ := 12*(p+1)*(n+1) + 3*n + 10

theorem extract_exec (n p : ℕ) (hp : 0 < p) :
    ∃ t, extract.Exec (state n p 0) (state (n/p) p (n%p)) t ∧
      t ≤ extractBound n p := by
  obtain ⟨u, hu, hub⟩ := UnaryDivision.divide_exec true n p hp
  let mid := UnaryDivision.store true 0 p 0 (n/p) (n%p)
  have ht : (transferProg (3 : Fin 6) (fun k => decide (k=0))).Exec mid
      (state (n/p) p (n%p)) (3*(n/p)+1) := by
    convert stack_transfer (3 : Fin 6) (fun k => decide (k=0)) mid using 1 <;>
      first | rfl |
        exact funext (fun k => by fin_cases k <;>
          simp [mid, state, UnaryDivision.store, transferStore]) |
        solve | simp [mid, UnaryDivision.store]
  refine ⟨_, hu.seq ht, ?_⟩
  have hq := Nat.div_le_self n p
  unfold extractBound
  omega

/-- Use six selected tapes to extract a digit while preserving every other tape. -/
theorem extractOn_exec {K : Type} [DecidableEq K] (e : Fin 6 ↪ K) (s : K → List Bool)
    (n p : ℕ) (hp : 0 < p)
    (hn : s (e 0) = List.replicate n true) (hd : s (e 1) = List.replicate p true)
    (h2 : s (e 2) = []) (h3 : s (e 3) = []) (h4 : s (e 4) = []) (h5 : s (e 5) = []) :
    ∃ t, (onPorts e extract).Exec s
      (Function.update (Function.update s (e 0) (List.replicate (n/p) true)) (e 4)
        (List.replicate (n%p) true)) t ∧ t ≤ extractBound n p := by
  obtain ⟨t, ht, hb⟩ := extract_exec n p hp
  refine ⟨t, onPorts_exec e ht ?_ ?_ ?_, hb⟩
  · intro k
    fin_cases k <;> simp [state, hn, hd, h2, h3, h4, h5]
  · intro k
    fin_cases k <;>
      simp [state, e.injective.eq_iff, hd, h2, h3, h5]
  · intro k hk
    simp only [Function.update_of_ne (Ne.symm (hk 4)), Function.update_of_ne (Ne.symm (hk 0))]

private def digitPorts : Fin 4 → Fin 6 ↪ Fin 9 := ![
  ⟨![0,1,2,3,4,8], by decide⟩, ⟨![0,1,2,3,5,8], by decide⟩,
  ⟨![0,1,2,3,6,8], by decide⟩, ⟨![0,1,2,3,7,8], by decide⟩]

def radixStore (n p : ℕ) (d : Fin 4 → ℕ) : Fin 9 → List Bool :=
  ![List.replicate n true, List.replicate p true, [], [],
    List.replicate (d 0) true, List.replicate (d 1) true,
    List.replicate (d 2) true, List.replicate (d 3) true, []]

private theorem extractDigit_exec (n p : ℕ) (hp : 0 < p) (d : Fin 4 → ℕ)
    (i : Fin 4) (hi : d i = 0) :
    ∃ t, (onPorts (digitPorts i) extract).Exec (radixStore n p d)
      (radixStore (n/p) p (Function.update d i (n%p))) t ∧ t ≤ extractBound n p := by
  let s := radixStore n p d
  have hd : s (digitPorts i 4) = [] := by
    fin_cases i <;> simp_all [s, digitPorts, radixStore]
  obtain ⟨u, hu, hub⟩ := extractOn_exec (digitPorts i) s n p hp
    (by fin_cases i <;> rfl) (by fin_cases i <;> rfl)
    (by fin_cases i <;> rfl) (by fin_cases i <;> rfl) hd (by fin_cases i <;> rfl)
  refine ⟨u, ?_, hub⟩
  convert hu using 1
  exact funext (fun k => by fin_cases i <;> fin_cases k <;> rfl)

def digits (n p k : ℕ) (i : Fin 4) : ℕ :=
  if i.val < k then (n/p^i.val)%p else 0

/-- Expose a fixed prefix of the base-`p` digits, least significant first. -/
noncomputable def decode : (k : ℕ) → k ≤ 4 → StackProg (Fin 9) Bool
  | 0, _ => .act (fun _ _ => .keep)
  | k+1, h => .seq (decode k (Nat.le_of_succ_le h)) (onPorts (digitPorts ⟨k,h⟩) extract)

theorem decode_exec (n p : ℕ) (hp : 0 < p) (k : ℕ) (hk : k ≤ 4) :
    ∃ t, (decode k hk).Exec (radixStore n p (fun _ => 0))
      (radixStore (n/p^k) p (digits n p k)) t ∧
      t ≤ k * (extractBound n p + 1) + 1 := by
  induction k with
  | zero =>
      have hzero : digits n p 0 = fun _ => 0 := by
        funext i
        simp [digits]
      rw [hzero, pow_zero, Nat.div_one]
      exact ⟨1, StackProg.Exec.act (fun _ _ => .keep) _, by simp⟩
  | succ k ih =>
      let i : Fin 4 := ⟨k,hk⟩
      let x := n/p^k
      have hzero : digits n p k i = 0 := by simp [digits, i]
      obtain ⟨u, hu, huB⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨v, hv, hvB⟩ := extractDigit_exec x p hp (digits n p k) i hzero
      have hq : x/p = n/p^(k+1) := by
        simp only [x, Nat.div_div_eq_div_mul, pow_succ]
      have hdigits : Function.update (digits n p k) i (x%p) = digits n p (k+1) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [digits, x, i]
        · have hne : j.val ≠ k := fun h => hj (Fin.ext h)
          have hiff : j.val < k+1 ↔ j.val < k := by omega
          simp [digits, hj, hiff]
      rw [hq, hdigits] at hv
      refine ⟨u+1+v, hu.seq hv, ?_⟩
      have hx : x ≤ n := Nat.div_le_self _ _
      have hmono : extractBound x p ≤ extractBound n p := by
        unfold extractBound
        gcongr
      simp only [Nat.succ_mul]
      omega

end FourToOneGames.WordMachines.Radix

end

/- CountedOutput -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines

open CookPvsNP

variable {K A : Type} [DecidableEq K]

/-- The count and output tapes of a traversal. The rest of the frame is preserved. -/
def countFrame (frame : K → List A) (counter out : K) (token : A) (n : ℕ)
    (tail : List A) : K → List A :=
  Function.update (Function.update frame counter (List.replicate n token)) out tail

/-- A body reads the decremented index and prepends that entry to the output tape. -/
def emitCounted (counter : K) (body : StackProg K A) : StackProg K A :=
  .loop (fun h => (h counter).isSome) (.seq (popProg counter) body)

def ascendingWords (entry : ℕ → List A) (n : ℕ) : List A :=
  (List.range n).flatMap entry

/-- A reverse traversal with prepending emits the entries in ascending order. -/
theorem emitCounted_exec (frame : K → List A) (counter out : K) (hne : out ≠ counter)
    (token : A) (body : StackProg K A) (entry : ℕ → List A) (n budget : ℕ)
    (hbody : ∀ i < n, ∀ tail : List A, ∃ steps,
      body.Exec (countFrame frame counter out token i tail)
        (countFrame frame counter out token i (entry i ++ tail)) steps ∧ steps ≤ budget)
    (tail : List A) :
    ∃ t, (emitCounted counter body).Exec (countFrame frame counter out token n tail)
      (countFrame frame counter out token 0 (ascendingWords entry n ++ tail)) t ∧
      t ≤ n * (budget + 4) + 1 := by
  induction n generalizing tail with
  | zero =>
      refine ⟨1, ?_, by simp⟩
      simpa [ascendingWords, emitCounted] using
        (StackProg.Exec.loopFalse (test := fun h => (h counter).isSome)
          (p := .seq (popProg counter) body) (s := countFrame frame counter out token 0 tail)
          (by simp [countFrame, Ne.symm hne]))
  | succ n ih =>
      obtain ⟨u, hu, huB⟩ := hbody n (Nat.lt_succ_self n) tail
      obtain ⟨v, hv, hvB⟩ := ih
        (fun i hi => hbody i (hi.trans (Nat.lt_succ_self n))) (entry n ++ tail)
      let before := countFrame frame counter out token (n+1) tail
      let after := countFrame frame counter out token n tail
      have hbefore : before counter = List.replicate (n+1) token := by
        simp [before, countFrame, Ne.symm hne]
      have hg : (before counter).head?.isSome = true := by simp [hbefore, List.replicate_succ]
      have hp : (popProg counter).Exec before after 1 := by
        convert pop_exec counter before using 1
        exact funext (fun k => by
          by_cases hk : k = counter <;> by_cases ho : k = out <;>
            simp [before, after, countFrame, hk, ho, hne, Ne.symm hne, List.replicate_succ])
      have he := StackProg.Exec.loopTrue (test := fun h => (h counter).isSome) hg
        (hp.seq hu) hv
      refine ⟨1+(1+1+u)+1+v, ?_, ?_⟩
      · simpa only [emitCounted, ascendingWords, List.range_succ, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] using he
      · simp only [Nat.succ_mul]
        omega

/-- Ports zero and one are the row and column counters, port two the output,
port three the retained column limit, and port four the copy scratch tape. -/
def rectangleFrame (ports : Fin 5 ↪ K) (frame : K → List A) (token : A)
    (row col : ℕ) (tail : List A) : K → List A :=
  countFrame (Function.update frame (ports 0) (List.replicate row token))
    (ports 1) (ports 2) token col tail

def emitRectangle (ports : Fin 5 ↪ K) (entry : StackProg K A) : StackProg K A :=
  emitCounted (ports 0) (.seq (copyProg (ports 3) (ports 1) (ports 4))
    (emitCounted (ports 1) entry))

def rectangleWords (entry : ℕ → ℕ → List A) (rows cols : ℕ) : List A :=
  ascendingWords (fun i => ascendingWords (entry i) cols) rows

private theorem rectangle_empty_column (ports : Fin 5 ↪ K) (frame : K → List A)
    (token : A) (row : ℕ) (tail : List A) :
    rectangleFrame ports frame token row 0 tail =
      countFrame (Function.update frame (ports 1) []) (ports 0) (ports 2) token row tail := by
  unfold rectangleFrame countFrame
  rw [List.replicate_zero, Function.update_comm (ports.injective.ne (by decide : (0 : Fin 5) ≠ 1))]

private theorem fillColumns_exec (ports : Fin 5 ↪ K) (frame : K → List A)
    (token : A) (row cols : ℕ) (tail : List A)
    (hlimit : frame (ports 3) = List.replicate cols token) (hwork : frame (ports 4) = []) :
    (copyProg (ports 3) (ports 1) (ports 4)).Exec
      (rectangleFrame ports frame token row 0 tail)
      (rectangleFrame ports frame token row cols tail) (6*cols+3) := by
  let s := rectangleFrame ports frame token row 0 tail
  have hleft : s (ports 3) = List.replicate cols token := by
    simp [s, rectangleFrame, countFrame, ports.injective.eq_iff, hlimit]
  have hcol : s (ports 1) = [] := by
    simp [s, rectangleFrame, countFrame, ports.injective.eq_iff]
  have hempty : s (ports 4) = [] := by
    simp [s, rectangleFrame, countFrame, ports.injective.eq_iff, hwork]
  have hup : Function.update s (ports 1) (s (ports 3) ++ s (ports 1)) =
      rectangleFrame ports frame token row cols tail := by
    rw [hleft, hcol, List.append_nil]
    unfold s rectangleFrame countFrame
    rw [Function.update_comm (ports.injective.ne (by decide : (2 : Fin 5) ≠ 1)),
      Function.update_idem]
  have hcopy := stack_copy (ports 3) (ports 1) (ports 4)
    (ports.injective.ne (by decide)) (ports.injective.ne (by decide))
    (ports.injective.ne (by decide)) s hempty
  rw [hup] at hcopy
  simpa only [hleft, List.length_replicate] using hcopy

/-- Reset the column counter at each row and emit a dense row-major table. -/
theorem emitRectangle_exec (ports : Fin 5 ↪ K) (frame : K → List A)
    (token : A) (rows cols : ℕ) (body : StackProg K A) (entry : ℕ → ℕ → List A)
    (budget : ℕ) (tail : List A)
    (hlimit : frame (ports 3) = List.replicate cols token) (hwork : frame (ports 4) = [])
    (hbody : ∀ i < rows, ∀ j < cols, ∀ w : List A, ∃ steps,
      body.Exec (rectangleFrame ports frame token i j w)
        (rectangleFrame ports frame token i j (entry i j ++ w)) steps ∧ steps ≤ budget) :
    ∃ t, (emitRectangle ports body).Exec (rectangleFrame ports frame token rows 0 tail)
      (rectangleFrame ports frame token 0 0 (rectangleWords entry rows cols ++ tail)) t ∧
      t ≤ rows * (cols * (budget+4) + 6*cols + 9) + 1 := by
  have hstep (i : ℕ) (hi : i < rows) (w : List A) :
      ∃ t, (StackProg.seq (copyProg (ports 3) (ports 1) (ports 4)) (emitCounted (ports 1) body)).Exec
        (rectangleFrame ports frame token i 0 w)
        (rectangleFrame ports frame token i 0 (ascendingWords (entry i) cols ++ w)) t ∧
        t ≤ cols * (budget+4) + 6*cols + 5 := by
    obtain ⟨u, hu, hbu⟩ := emitCounted_exec
      (Function.update frame (ports 0) (List.replicate i token)) (ports 1) (ports 2)
      (ports.injective.ne (by decide)) token body (entry i) cols budget (hbody i hi) w
    exact ⟨_, (fillColumns_exec ports frame token i cols w hlimit hwork).seq hu, by omega⟩
  have h := emitCounted_exec (Function.update frame (ports 1) []) (ports 0) (ports 2)
    (ports.injective.ne (by decide)) token
    (.seq (copyProg (ports 3) (ports 1) (ports 4)) (emitCounted (ports 1) body))
    (fun i => ascendingWords (entry i) cols) rows (cols * (budget + 4) + 6*cols + 5)
    (fun i hi w => by simpa only [rectangle_empty_column] using hstep i hi w) tail
  simpa only [rectangle_empty_column, emitRectangle, rectangleWords, Nat.add_assoc,
    show 5+4=9 by decide] using h

end FourToOneGames.WordMachines

end

/- FourToOneReduction -/
section

/-!
The affine simple-graph lift and the Label Cover to binary 3SAT reduction use
the exact Prove2Me definitions. The composition is proved with explicit TM2
certificate premises for the two encoding transformations.
-/

section Mixing

namespace FourToOneGames

open scoped BigOperators

/-- An absolute discrepancy bound for sums of orthogonal rows over two subsets. -/
theorem rectangle_sq_bound {X Y : Type} [Fintype Y] (g : X → Y → ℝ)
    (B : ℝ) (S : Finset X) (T : Finset Y)
    (hdiag : ∀ x ∈ S, ∑ y, (g x y)^2 ≤ B)
    (hoff : ∀ x ∈ S, ∀ x' ∈ S, x' ≠ x → ∑ y, g x y * g x' y = 0) :
    (∑ y ∈ T, ∑ x ∈ S, g x y)^2 ≤ (T.card : ℝ) * (S.card : ℝ) * B := by
  classical
  let h (y : Y) := ∑ x ∈ S, g x y
  have hCS : (∑ y ∈ T, h y)^2 ≤ (T.card : ℝ) * ∑ y ∈ T, (h y)^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) h
  have hexpand : (∑ y, (h y)^2) = ∑ x ∈ S, ∑ x' ∈ S, ∑ y, g x y * g x' y := by
    simp only [h, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hdiagSum : (∑ y, (h y)^2) ≤ (S.card : ℝ) * B := by
    rw [hexpand, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro x hx
    rw [Finset.sum_eq_single x (fun x' hx' hne => hoff x hx x' hx' hne)
      (fun h => (h hx).elim)]
    simpa only [pow_two] using hdiag x hx
  have hpart : (∑ y ∈ T, (h y)^2) ≤ ∑ y, (h y)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  exact hCS.trans (by rw [mul_assoc]; gcongr; exact hpart.trans hdiagSum)

end FourToOneGames

end Mixing

section AffineTags

namespace FourToOneGames.AffineTags

open scoped BigOperators

abbrev Point (p : ℕ) := Fin 3 → ZMod p
abbrev Seed (p : ℕ) := Point p × ZMod p

/-- The tag is the value of the affine functional specified by the right copy. -/
def tag {p : ℕ} (x : Point p) (y : Seed p) : ZMod p :=
  (∑ i, x i * y.1 i) + y.2

private theorem tag_sub {p : ℕ} (x x' : Point p) (y : Seed p) :
    tag x y - tag x' y = ∑ i, (x i - x' i) * y.1 i := by
  unfold tag
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

private def oneFiberEquiv {p : ℕ} (x : Point p) (t : ZMod p) :
    {y : Seed p // tag x y = t} ≃ Point p where
  toFun y := y.1.1
  invFun b := ⟨(b, t - ∑ i, x i * b i), by simp [tag]⟩
  left_inv y := by
    apply Subtype.ext
    have hc : t - (∑ i, x i * y.1.1 i) = y.1.2 := by
      have ht := congrArg (· - ∑ i, x i * y.1.1 i) y.2.symm
      simpa only [tag, add_sub_cancel_left] using ht
    exact Prod.ext rfl hc
  right_inv _ := rfl

theorem card_point (p : ℕ) [NeZero p] : Fintype.card (Point p) = p ^ 3 := by
  simp [Point, ZMod.card]

theorem card_seed (p : ℕ) [NeZero p] : Fintype.card (Seed p) = p ^ 4 := by
  simp [Seed, ZMod.card, pow_succ p 3]

/-- For any left copy, every tag selects the same number of right copies. -/
theorem card_tag_fiber {p : ℕ} [NeZero p] (x : Point p) (t : ZMod p) :
    Fintype.card {y : Seed p // tag x y = t} = p ^ 3 :=
  (Fintype.card_congr (oneFiberEquiv x t)).trans (card_point p)

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Two distinct left copies have independent tags on a uniform right copy. -/
theorem card_tag_pair (x x' : Point p) (hne : x ≠ x') (t t' : ZMod p) :
    Fintype.card {y : Seed p // tag x y = t ∧ tag x' y = t'} = p ^ 2 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  let α := {j : Fin 3 // j ≠ i}
  let f (y : {y : Seed p // tag x y = t ∧ tag x' y = t'}) : α → ZMod p := fun j => y.1.1 j.1
  have hΔ : x i - x' i ≠ 0 := sub_ne_zero.mpr hi
  have heq (y : {y : Seed p // tag x y = t ∧ tag x' y = t'}) :
      (∑ j ∈ Finset.univ.erase i, (x j - x' j) * y.1.1 j) +
        (x i - x' i) * y.1.1 i = t - t' := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i), ← tag_sub, y.2.1, y.2.2]
  have hf : Function.Bijective f := by
    constructor
    · intro y z h
      have hRest :
          (∑ j ∈ Finset.univ.erase i, (x j - x' j) * y.1.1 j) =
          (∑ j ∈ Finset.univ.erase i, (x j - x' j) * z.1.1 j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg ((x j - x' j) * ·) (congrFun h ⟨j, (Finset.mem_erase.mp hj).1⟩)
      have hAt : y.1.1 i = z.1.1 i := by
        have hy := heq y
        rw [hRest, ← heq z] at hy
        exact mul_left_cancel₀ hΔ (add_left_cancel hy)
      have hBase : y.1.1 = z.1.1 := by
        funext j
        by_cases hj : j = i
        · simpa [hj] using hAt
        · exact congrFun h ⟨j, hj⟩
      apply Subtype.ext
      apply Prod.ext hBase
      have hy := y.2.1.trans z.2.1.symm
      simp only [tag, hBase] at hy
      exact add_left_cancel hy
    · intro u
      let b₀ (j : Fin 3) : ZMod p := if h : j = i then 0 else u ⟨j, h⟩
      let other := ∑ j ∈ Finset.univ.erase i, (x j - x' j) * b₀ j
      let a := (t - t' - other) / (x i - x' i)
      let b (j : Fin 3) : ZMod p := if h : j = i then a else u ⟨j, h⟩
      let y : Seed p := (b, t - ∑ j, x j * b j)
      have htag : tag x y = t := by simp [tag, y]
      have hsum : (∑ j, (x j - x' j) * b j) = t - t' := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        have hOther : (∑ j ∈ Finset.univ.erase i, (x j - x' j) * b j) = other := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [b, b₀, (Finset.mem_erase.mp hj).1]
        rw [hOther, show b i = a by simp [b]]
        dsimp only [a]
        field_simp
        ring
      have htag' : tag x' y = t' := by
        have h := tag_sub x x' y
        change tag x y - tag x' y = _ at h
        rw [htag, show (∑ j, (x j - x' j) * y.1 j) = t - t' from hsum] at h
        exact sub_right_inj.mp h
      refine ⟨⟨y, htag, htag'⟩, ?_⟩
      funext j
      change b j.1 = u j
      simp [b, j.2]
  let e := Equiv.ofBijective f hf
  have hα : Fintype.card α = 2 := by
    change Fintype.card {j : Fin 3 // ¬ j = i} = 2
    rw [Fintype.card_subtype_compl (fun j : Fin 3 => j = i)]
    simp
  simpa [Fintype.card_fun, ZMod.card, hα] using Fintype.card_congr e

end FourToOneGames.AffineTags

end AffineTags

section TagMixing

namespace FourToOneGames.AffineTags

open scoped BigOperators

private theorem sum_indicator {Y : Type} [Fintype Y] (P : Y → Prop) [DecidablePred P] :
    (∑ y, if P y then (1 : ℝ) else 0) = Fintype.card {y // P y} := by
  rw [← Finset.sum_filter]
  simp [Fintype.card_subtype]

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- For each tag, a rectangle contains at most its product-density prediction plus
(p^5) edges. There are (p^6) pairs of copies having the tag in the full rectangle. -/
theorem tag_rectangle_le (S : Finset (Point p)) (T : Finset (Seed p)) (t : ZMod p) :
    (((T.product S).filter fun yx => tag yx.2 yx.1 = t).card : ℝ) ≤
      (T.card : ℝ) * S.card / p + (p : ℝ)^5 := by
  classical
  let n := (p : ℝ)
  let m (x : Point p) (y : Seed p) : ℝ := if tag x y = t then 1 else 0
  let g (x : Point p) (y : Seed p) : ℝ := n * m x y - 1
  have hp : 0 < n := by
    change (0 : ℝ) < p
    exact_mod_cast (Fact.out : p.Prime).pos
  have hc : (Fintype.card (Seed p) : ℝ) = n ^ 4 := by
    dsimp only [n]
    exact_mod_cast card_seed p
  have hm (x : Point p) : ∑ y, m x y = n ^ 3 := by
    rw [show (∑ y, m x y) = Fintype.card {y // tag x y = t} from sum_indicator _,
      card_tag_fiber]
    simp [n]
  have hmm (x x' : Point p) (hx : x' ≠ x) : ∑ y, m x y * m x' y = n ^ 2 := by
    have h (y : Seed p) : m x y * m x' y =
        if tag x y = t ∧ tag x' y = t then 1 else 0 := by
      by_cases h1 : tag x y = t <;> by_cases h2 : tag x' y = t <;> simp [m, h1, h2]
    simp_rw [h]
    rw [sum_indicator, card_tag_pair x x' hx.symm]
    simp [n]
  have hdiag (x : Point p) : ∑ y, (g x y)^2 ≤ n ^ 5 := by
    have h (y : Seed p) : (g x y)^2 = n^2 * m x y - (2*n) * m x y + 1 := by
      by_cases hx : tag x y = t
      · simp [g, m, hx]; ring
      · simp [g, m, hx]
    simp_rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hm]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hc]
    nlinarith [pow_nonneg hp.le 4]
  have hoff (x x' : Point p) (hx : x' ≠ x) : ∑ y, g x y * g x' y = 0 := by
    have h (y : Seed p) : g x y * g x' y =
        n^2 * (m x y * m x' y) - n * m x y - n * m x' y + 1 := by
      dsimp [g]
      ring
    simp_rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hm, hmm x x' hx]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hc]
    ring
  have hs : (S.card : ℝ) ≤ n ^ 3 := by
    rw [← show (Fintype.card (Point p) : ℝ) = n^3 by dsimp only [n]; exact_mod_cast card_point p]
    exact_mod_cast Finset.card_le_univ S
  have ht : (T.card : ℝ) ≤ n ^ 4 := by
    rw [← hc]
    exact_mod_cast Finset.card_le_univ T
  let M := ((T.product S).filter fun yx => tag yx.2 yx.1 = t).card
  have hsum : (∑ y ∈ T, ∑ x ∈ S, m x y) = (M : ℝ) := by
    unfold M
    calc
      _ = ∑ yx ∈ T.product S, m yx.2 yx.1 :=
        (Finset.sum_product T S (fun yx : Seed p × Point p => m yx.2 yx.1)).symm
      _ = _ := by simp [m]
  have hcenter : (∑ y ∈ T, ∑ x ∈ S, g x y) = n * M - (T.card : ℝ) * S.card := by
    simp only [g, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul, mul_one, hsum]
  have hbig : (∑ y ∈ T, ∑ x ∈ S, g x y)^2 ≤ (n^6)^2 := calc
    _ ≤ (T.card : ℝ) * S.card * n^5 :=
      rectangle_sq_bound g (n^5) S T (fun x _ => hdiag x) (fun x _ x' _ => hoff x x')
    _ ≤ n^4 * n^3 * n^5 := by gcongr
    _ = _ := by ring
  rw [hcenter] at hbig
  have hupper : n * M - (T.card : ℝ) * S.card ≤ n^6 := by
    by_contra! h
    have hpos : 0 < n^6 := pow_pos hp _
    nlinarith
  change (M : ℝ) ≤ (T.card : ℝ) * S.card / n + n^5
  calc
    _ ≤ ((T.card : ℝ) * S.card + n^6) / n := (le_div_iff₀ hp).mpr (by linarith)
    _ = _ := by rw [add_div, pow_succ n 5, mul_div_cancel_right₀ _ hp.ne']

end FourToOneGames.AffineTags

end TagMixing

section TaggedProjection

namespace FourToOneGames.AffineTags

open scoped BigOperators

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- For a projection constraint, sum the rectangle estimates over the left labels. -/
theorem tag_projection_le {A B : Type} [Fintype A] [DecidableEq B]
    (l : Point p → A) (r : Seed p → B) (proj : A → B) (t : ZMod p) :
      ((Finset.univ.filter fun yx : Seed p × Point p =>
      proj (l yx.2) = r yx.1 ∧ tag yx.2 yx.1 = t).card : ℝ) ≤
      ((Finset.univ.filter fun yx : Seed p × Point p =>
        proj (l yx.2) = r yx.1).card : ℝ) / p + (Fintype.card A : ℝ) * (p:ℝ)^5 := by
  classical
  let S (a : A) := Finset.univ.filter (fun x => l x = a)
  let T (a : A) := Finset.univ.filter (fun y => proj a = r y)
  let R (a : A) := T a ×ˢ S a
  let good (yx : Seed p × Point p) := proj (l yx.2) = r yx.1
  let marked (yx : Seed p × Point p) := tag yx.2 yx.1 = t
  have hpart (P : Seed p × Point p → Prop) [DecidablePred P] :
      (Finset.univ.filter fun z => good z ∧ P z).card =
        ∑ a, ((R a).filter P).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun z => l z.2)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, R, S, T, Finset.mem_product, good]
    constructor
    · rintro ⟨⟨h, hp⟩, ha⟩
      exact ⟨⟨by simpa only [ha] using h, ha⟩, hp⟩
    · rintro ⟨⟨h, ha⟩, hp⟩
      exact ⟨⟨by simpa only [ha] using h, hp⟩, ha⟩
  have hfull : (Finset.univ.filter good).card = ∑ a, (R a).card := by
    simpa using hpart (fun _ => True)
  change (((Finset.univ.filter fun z => good z ∧ marked z).card : ℕ) : ℝ) ≤ _
  rw [hpart marked, Nat.cast_sum]
  have hle : (∑ a, (((R a).filter marked).card : ℝ)) ≤
      (∑ a, ((R a).card : ℝ) / p) + (Fintype.card A : ℝ) * (p:ℝ)^5 := by
    calc
      _ ≤ ∑ a, (((R a).card : ℝ) / p + (p:ℝ)^5) := by
        apply Finset.sum_le_sum
        intro a _
        have he : (R a).filter marked =
            ((T a).product (S a)).filter (fun z => tag z.2 z.1 = t) := by
          ext z
          simp only [Finset.mem_filter, marked]
          rfl
        rw [he, show (R a).card = (T a).card * (S a).card from Finset.card_product .., Nat.cast_mul]
        exact tag_rectangle_le (S a) (T a) t
      _ = _ := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
  change _ ≤ (((Finset.univ.filter good).card : ℕ) : ℝ) / p + _
  rw [hfull, Nat.cast_sum, Finset.sum_div]
  exact hle

end FourToOneGames.AffineTags

end TaggedProjection

section SimpleLiftValue

set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace FourToOneGames

open OAI.PerfectCompleteness AffineTags
open scoped BigOperators

namespace SimpleLift

variable {p q : ℕ} [Fact (Nat.Prime p)]

private def coordEquiv : (Fin 3 → ZMod p) ≃ ZMod p × ZMod p × ZMod p where
  toFun x := (x 0, x 1, x 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by rcases x with ⟨a,b,c⟩; rfl

private def pointIndex : Point p ≃ Fin (p^3) :=
  let e := (ZMod.finEquiv p).toEquiv.symm
  coordEquiv.trans ((e.prodCongr ((e.prodCongr e).trans finProdFinEquiv)).trans
    (finProdFinEquiv.trans (finCongr (by ring))))

private def seedIndex : Seed p ≃ Fin (p^4) :=
  (pointIndex.prodCongr (ZMod.finEquiv p).toEquiv.symm).trans
    (finProdFinEquiv.trans (finCongr (by ring)))

/-- Copy indices use mixed radix, in the same order as the encoded vertex IDs. -/
def leftIndex (G : Instance q) : Fin G.leftVertices × Point p ≃ Fin (G.leftVertices * p^3) :=
  ((Equiv.refl _).prodCongr pointIndex).trans finProdFinEquiv

def rightIndex (G : Instance q) : Fin G.rightVertices × Seed p ≃ Fin (G.rightVertices * p^4) :=
  ((Equiv.refl _).prodCongr seedIndex).trans finProdFinEquiv

/-- Each left label is replaced by two labels giving the same projection. -/
def labelIndex (q : ℕ) : Fin (2*q) × Fin 2 ≃ Fin (4*q) :=
  finProdFinEquiv.trans (finCongr (by ring))

abbrev Copies (t : ZMod p) := {yx : Seed p × Point p // tag yx.2 yx.1 = t}

private def copiesEquiv (t : ZMod p) : Copies t ≃ Σ x : Point p, {y : Seed p // tag x y = t} where
  toFun z := ⟨z.1.2, z.1.1, z.2⟩
  invFun z := ⟨(z.2.1, z.1), z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_copies (t : ZMod p) : Fintype.card (Copies t) = p^6 := by
  rw [Fintype.card_congr (copiesEquiv t), Fintype.card_sigma]
  simp [card_tag_fiber]
  ring

private abbrev EdgeSource (G : Instance q) :=
  Σ i : Fin G.edges.length, Copies (i.val : ZMod p)

private def edgePair (G : Instance q) (e : EdgeSource (p := p) G) :
    Fin (G.leftVertices * p^3) × Fin (G.rightVertices * p^4) :=
  (leftIndex G ((G.edges.get e.1).left, e.2.1.2),
    rightIndex G ((G.edges.get e.1).right, e.2.1.1))

private theorem tagValue (G : Instance q) (hp : G.edges.length ≤ p) (e : EdgeSource (p := p) G) :
    (tag e.2.1.2 e.2.1.1).val = e.1.val := by
  rw [e.2.2, ZMod.val_natCast, Nat.mod_eq_of_lt (e.1.isLt.trans_le hp)]

private theorem edgePair_injective (G : Instance q) (hp : G.edges.length ≤ p) :
    Function.Injective (edgePair (p := p) G) := by
  intro e f h
  have hx : e.2.1.2 = f.2.1.2 :=
    congrArg (Prod.snd : Fin G.leftVertices × Point p → Point p)
      ((leftIndex G).injective (congrArg Prod.fst h))
  have hy : e.2.1.1 = f.2.1.1 :=
    congrArg (Prod.snd : Fin G.rightVertices × Seed p → Seed p)
      ((rightIndex G).injective (congrArg Prod.snd h))
  have htag : e.1 = f.1 := by
    apply Fin.ext
    rw [← tagValue G hp e, ← tagValue G hp f, hx, hy]
  rcases e with ⟨i,a⟩
  rcases f with ⟨j,b⟩
  change i = j at htag
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext (Prod.ext hy hx))

/-- A parallel constraint is placed only on copy pairs having its own tag. -/
@[reducible] noncomputable def game (G : Instance q) (hq : 0 < q) (hp : G.edges.length ≤ p) :
    LabelCover where
  nL := G.leftVertices * p^3
  nR := G.rightVertices * p^4
  sizeL := 4*q
  sizeR := q
  edges := Finset.univ.map ⟨edgePair G, edgePair_injective G hp⟩
  proj u v a :=
    let id := (tag ((leftIndex G).symm u).2 ((rightIndex G).symm v).2).val
    if h : id < G.edges.length then
      (G.edges.get ⟨id, h⟩).projection.images[((labelIndex q).symm a).1]
    else ⟨0, hq⟩

/-- The record ordinal encoded by the pair of copy indices. -/
def edgeOrdinal (G : Instance q) (u : Fin (G.leftVertices * p^3))
    (v : Fin (G.rightVertices * p^4)) : ℕ :=
  (tag ((leftIndex G).symm u).2 ((rightIndex G).symm v).2).val

/-- A matrix entry of the lifted graph needs only one record lookup. -/
theorem game_edge_iff (G : Instance q) (hq : 0 < q) (hp : G.edges.length ≤ p)
    (u : Fin (G.leftVertices * p^3)) (v : Fin (G.rightVertices * p^4)) :
    (u,v) ∈ (game G hq hp).edges ↔
      ∃ h : edgeOrdinal G u v < G.edges.length,
        (G.edges.get ⟨edgeOrdinal G u v, h⟩).left = ((leftIndex G).symm u).1 ∧
        (G.edges.get ⟨edgeOrdinal G u v, h⟩).right = ((rightIndex G).symm v).1 := by
  constructor
  · intro hm
    obtain ⟨e, _, he⟩ := Finset.mem_map.mp hm
    change edgePair G e = (u,v) at he
    have hu : (edgePair G e).1 = u := congrArg Prod.fst he
    have hv : (edgePair G e).2 = v := congrArg Prod.snd he
    have htag : edgeOrdinal G u v = e.1.val := by
      rw [← hu, ← hv]
      simpa only [edgeOrdinal, edgePair, Equiv.symm_apply_apply] using tagValue G hp e
    have h : edgeOrdinal G u v < G.edges.length := htag ▸ e.1.isLt
    have hi : (⟨edgeOrdinal G u v, h⟩ : Fin G.edges.length) = e.1 := Fin.ext htag
    refine ⟨h, ?_⟩
    rw [hi]
    simp only [← hu, ← hv, edgePair, Equiv.symm_apply_apply, and_self]
  · rintro ⟨h, hl, hr⟩
    let i : Fin G.edges.length := ⟨edgeOrdinal G u v, h⟩
    let x := (leftIndex G).symm u
    let y := (rightIndex G).symm v
    have ht : tag x.2 y.2 = (i.val : ZMod p) := (ZMod.natCast_zmod_val _).symm
    let e : EdgeSource (p := p) G := ⟨i, ⟨(y.2,x.2), ht⟩⟩
    apply Finset.mem_map.mpr
    refine ⟨e, Finset.mem_univ _, ?_⟩
    change (leftIndex G ((G.edges.get i).left, x.2),
      rightIndex G ((G.edges.get i).right, y.2)) = (u,v)
    change (G.edges.get i).left = x.1 at hl
    change (G.edges.get i).right = y.1 at hr
    simp only [hl, hr, Prod.eta, x, y, Equiv.apply_symm_apply]

/-- The dense projection table uses the same record ordinal, including for nonedges. -/
theorem game_proj_eq (G : Instance q) (hq : 0 < q) (hp : G.edges.length ≤ p)
    (u : Fin (G.leftVertices * p^3)) (v : Fin (G.rightVertices * p^4)) (a : Fin (4*q)) :
    ((game G hq hp).proj u v a).val =
      if h : edgeOrdinal G u v < G.edges.length then
        ((G.edges.get ⟨edgeOrdinal G u v,h⟩).projection.images[((labelIndex q).symm a).1]).val
      else 0 := by
  simp only [game, edgeOrdinal]
  split <;> rfl

theorem leftIndex_symm_vertex (G : Instance q) (u : Fin (G.leftVertices * p^3)) :
    ((leftIndex G).symm u).1.val = u.val / p^3 := rfl

theorem rightIndex_symm_vertex (G : Instance q) (v : Fin (G.rightVertices * p^4)) :
    ((rightIndex G).symm v).1.val = v.val / p^4 := rfl

theorem labelIndex_symm_base (a : Fin (4*q)) :
    ((labelIndex q).symm a).1.val = a.val / 2 := rfl

theorem leftIndex_symm_coordinates (G : Instance q) (u : Fin (G.leftVertices * p^3)) :
    let x := ((leftIndex G).symm u).2
    let a := u.val % p^3
    (x 0).val = a / (p*p) ∧ (x 1).val = a % (p*p) / p ∧
      (x 2).val = a % (p*p) % p := by
  cases p with
  | zero => exact (Nat.not_prime_zero Fact.out).elim
  | succ p => exact ⟨rfl, rfl, rfl⟩

theorem rightIndex_symm_coordinates (G : Instance q) (v : Fin (G.rightVertices * p^4)) :
    let y := ((rightIndex G).symm v).2
    let b := v.val % p^4
    let a := b / p
    (y.1 0).val = a / (p*p) ∧ (y.1 1).val = a % (p*p) / p ∧
      (y.1 2).val = a % (p*p) % p ∧ y.2.val = b % p := by
  cases p with
  | zero => exact (Nat.not_prime_zero Fact.out).elim
  | succ p => exact ⟨rfl, rfl, rfl, rfl⟩

/-- The tag can be evaluated by three natural products and a single remainder. -/
theorem tag_val_natural (x : Point p) (y : Seed p) :
    (tag x y).val =
      (y.2.val + (x 0).val * (y.1 0).val + (x 1).val * (y.1 1).val +
        (x 2).val * (y.1 2).val) % p := by
  have htag : tag x y =
      ((y.2.val + (x 0).val * (y.1 0).val + (x 1).val * (y.1 1).val +
        (x 2).val * (y.1 2).val : ℕ) : ZMod p) := by
    simp only [tag, Fin.sum_univ_three, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    ring
  rw [htag, ZMod.val_natCast]

private theorem proj_edge (G : Instance q) (hq : 0 < q) (hp : G.edges.length ≤ p)
    (e : EdgeSource (p := p) G) (a : Fin (4*q)) :
    (game G hq hp).proj (edgePair G e).1 (edgePair G e).2 a =
      (G.edges.get e.1).projection.images[((labelIndex q).symm a).1] := by
  have hId : (tag ((leftIndex G).symm (edgePair G e).1).2
      ((rightIndex G).symm (edgePair G e).2).2).val = e.1.val := by
    simpa only [edgePair, Equiv.symm_apply_apply] using tagValue G hp e
  simp only [game, hId, e.1.isLt, dite_true, Fin.eta]

theorem edge_count (G : Instance q) (hq : 0 < q) (hp : G.edges.length ≤ p) :
    (game G hq hp).edges.card = G.edges.length * p^6 := by
  simp [game, Fintype.card_sigma, card_copies]

private theorem card_projection (E : ProjectionTable q) (b : Fin q) :
    Fintype.card {a : Fin (2*q) // E.images[a] = b} = 2 := by
  rw [Fintype.card_subtype]
  have hND : ((List.finRange (2*q)).filter (fun a => decide (E.images[a] = b))).Nodup :=
    (List.nodup_finRange _).filter _
  have he : ((List.finRange (2*q)).filter (fun a => decide (E.images[a] = b))).toFinset =
      Finset.univ.filter (fun a : Fin (2*q) => E.images[a] = b) := by
    ext a
    simp
  rw [← he, List.toFinset_card_of_nodup hND]
  exact E.exactlyTwo b

/-- The lift is exactly four-to-one on every actual edge. -/
theorem isDToOne (G : Instance q) (hq : 0 < q) (hp : G.edges.length ≤ p) :
    (game G hq hp).IsDToOne 4 := by
  classical
  intro z hz b
  obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hz
  simp only [Function.Embedding.coeFn_mk]
  rw [← Fintype.card_subtype]
  let E := (G.edges.get e.1).projection
  let pred (a : Fin (4*q)) := (game G hq hp).proj (edgePair G e).1 (edgePair G e).2 a = b
  have he (a : Fin (4*q)) : pred a ↔ E.images[((labelIndex q).symm a).1] = b := by
    change (game G hq hp).proj (edgePair G e).1 (edgePair G e).2 a = b ↔ _
    exact iff_of_eq (congrArg (· = b) (proj_edge G hq hp e a))
  let e' : {a : Fin (4*q) // E.images[((labelIndex q).symm a).1] = b} ≃
      {a : Fin (2*q) × Fin 2 // E.images[a.1] = b} :=
    (labelIndex q).symm.subtypeEquiv (fun _ => Iff.rfl)
  let e'' : {a : Fin (2*q) × Fin 2 // E.images[a.1] = b} ≃
      {a : Fin (2*q) // E.images[a] = b} × Fin 2 :=
    Equiv.prodSubtypeFstEquivSubtypeProd (p := fun a : Fin (2*q) => E.images[a] = b)
  refine (Fintype.card_congr ((Equiv.subtypeEquivRight he).trans
    (e'.trans e''))).trans ?_
  rw [Fintype.card_prod, Fintype.card_fin]
  exact congrArg (· * 2) (card_projection E b)

private theorem sum_indicator_eq_card {A : Type} [Fintype A]
    (f : A → Prop) [DecidablePred f] :
    (∑ x, if f x then (1 : ℝ) else 0) = (Finset.univ.filter f).card := by
  rw [← Finset.sum_filter]
  simp

private theorem countSatisfied_eq_card {l r q : ℕ}
    (es : List (Edge l r q)) (A : Fin l → Fin (2*q)) (B : Fin r → Fin q) :
    countSatisfied A B es =
      (Finset.univ.filter fun i : Fin es.length =>
        (es.get i).projection.images[A (es.get i).left] = B (es.get i).right).card := by
  have h (es : List (Edge l r q)) :
      (Finset.univ.filter fun i : Fin es.length =>
        (es.get i).projection.images[A (es.get i).left] = B (es.get i).right).card =
      ∑ i : Fin es.length, if (es.get i).projection.images[A (es.get i).left] = B (es.get i).right
        then (1 : ℕ) else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [h]
  induction es with
  | nil => simp [countSatisfied]
  | cons e es ih =>
    simp only [List.length_cons, Fin.sum_univ_succ, List.get_cons_zero]
    by_cases hw : e.projection.images[A e.left] = B e.right <;>
      simp [countSatisfied, Edge.satisfied, ih, hw]

private theorem countSatisfied_le (G : Instance q) (A : Fin G.leftVertices → Fin (2*q))
    (B : Fin G.rightVertices → Fin q) :
    countSatisfied A B G.edges ≤ G.maxSatisfied := by
  unfold Instance.maxSatisfied
  exact Finset.le_sup (f := fun s : Labeling G => countSatisfied s.1 s.2 G.edges) (Finset.mem_univ (A,B))

private theorem valAssign_le_one (G : LabelCover) (A : Fin G.nL → Fin G.sizeL)
    (B : Fin G.nR → Fin G.sizeR) : G.valAssign A B ≤ 1 := by
  unfold LabelCover.valAssign
  by_cases he : G.edges.card = 0
  · simp [he]
  · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero he))).mpr
    exact_mod_cast Finset.card_filter_le _ _

set_option maxHeartbeats 1000000 in
/-- A perfect labeling of the multigraph lifts to a perfect labeling of the simple graph. -/
theorem complete (G : Instance q) (hq : 0 < q) (hp : G.edges.length ≤ p)
    (hc : G.value = 1) : (game G hq hp).val = 1 := by
  classical
  letI : Nonempty (Labeling G) := ⟨(fun _ => ⟨0, by omega⟩), (fun _ => ⟨0,hq⟩)⟩
  obtain ⟨A, _, hAMax⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Labeling G))
    Finset.univ_nonempty (fun x => countSatisfied x.1 x.2 G.edges)
  have hmpos : 0 < G.edges.length := List.length_pos_iff.mpr G.nonempty
  have hcnt : countSatisfied A.1 A.2 G.edges = G.edges.length := by
    unfold Instance.value at hc
    change G.maxSatisfied = _ at hAMax
    have he := (div_eq_iff (Nat.cast_ne_zero.mpr hmpos.ne')).mp hc
    rw [one_mul, hAMax] at he
    exact_mod_cast he
  have hAll (i : Fin G.edges.length) :
      (G.edges.get i).projection.images[A.1 (G.edges.get i).left] = A.2 (G.edges.get i).right := by
    rw [countSatisfied_eq_card] at hcnt
    have hAll := Finset.card_filter_eq_iff.mp (show
      (Finset.univ.filter fun j : Fin G.edges.length => (G.edges.get j).projection.images[
        A.1 (G.edges.get j).left] = A.2 (G.edges.get j).right).card = Finset.univ.card
          by simpa only [Finset.card_univ, Fintype.card_fin] using hcnt)
    exact hAll i (Finset.mem_univ _)
  let Q := game G hq hp
  let L (u : Fin Q.nL) : Fin Q.sizeL := labelIndex q (A.1 ((leftIndex G).symm u).1, 0)
  let R (v : Fin Q.nR) : Fin Q.sizeR := A.2 ((rightIndex G).symm v).1
  have hPerfect : Q.valAssign L R = 1 := by
    have hf : (Q.edges.filter fun z => Q.proj z.1 z.2 (L z.1) = R z.2) = Q.edges := by
      refine Finset.filter_eq_self.mpr ?_
      intro z hz
      obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hz
      have h := hAll e.1
      change (game G hq hp).proj (edgePair G e).1 (edgePair G e).2 (L (edgePair G e).1) =
        R (edgePair G e).2
      rw [proj_edge G hq hp e]
      simpa only [L, R, edgePair, Equiv.symm_apply_apply] using h
    have hne : (Q.edges.card : ℝ) ≠ 0 := by
      rw [edge_count]
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hmpos.ne'
        (pow_ne_zero _ (Fact.out : p.Prime).pos.ne'))
    change ((Q.edges.filter fun z => Q.proj z.1 z.2 (L z.1) = R z.2).card : ℝ) /
      (Q.edges.card : ℝ) = 1
    rw [hf, div_self hne]
  have hBound : BddAbove (Set.range fun b : (Fin Q.nL → Fin Q.sizeL) × (Fin Q.nR → Fin Q.sizeR) =>
      Q.valAssign b.1 b.2) := ⟨1, fun _ ⟨_, hr⟩ => hr ▸ valAssign_le_one Q _ _⟩
  letI : Nonempty ((Fin Q.nL → Fin Q.sizeL) × (Fin Q.nR → Fin Q.sizeR)) := ⟨L,R⟩
  refine le_antisymm (ciSup_le fun b => valAssign_le_one Q b.1 b.2) ?_
  calc
    1 = Q.valAssign L R := hPerfect.symm
    _ ≤ Q.val := le_ciSup hBound (L,R)

set_option maxHeartbeats 1000000 in
/-- For any labeling of the simple graph, the fraction of satisfied edges is at
most the multigraph value plus (2q/p). The copy pair is averaged globally. -/
theorem sound (G : Instance q) (hq : 0 < q) (hp : G.edges.length ≤ p) :
    (game G hq hp).val ≤ G.value + (2*q : ℝ) / p := by
  classical
  let Q := game G hq hp
  letI : Nonempty ((Fin Q.nL → Fin Q.sizeL) × (Fin Q.nR → Fin Q.sizeR)) :=
    ⟨(fun _ => ⟨0, by change 0 < 4*q; omega⟩), (fun _ => ⟨0,hq⟩)⟩
  apply ciSup_le
  intro A
  let l (u : Fin G.leftVertices) (x : Point p) :=
    ((labelIndex q).symm (A.1 (leftIndex G (u,x)))).1
  let r (v : Fin G.rightVertices) (y : Seed p) := A.2 (rightIndex G (v,y))
  let good (i : Fin G.edges.length) (z : Seed p × Point p) :=
    (G.edges.get i).projection.images[l (G.edges.get i).left z.2] = r (G.edges.get i).right z.1
  let cnt (i : Fin G.edges.length) := (Finset.univ.filter (good i)).card
  let marked (i : Fin G.edges.length) := (Finset.univ.filter fun z =>
    good i z ∧ tag z.2 z.1 = (i.val : ZMod p)).card
  let sat (z : Fin Q.nL × Fin Q.nR) := Q.proj z.1 z.2 (A.1 z.1) = A.2 z.2
  have hSat (e : EdgeSource (p := p) G) : sat (edgePair G e) ↔ good e.1 e.2.1 := by
    change Q.proj (edgePair G e).1 (edgePair G e).2 (A.1 (edgePair G e).1) =
        A.2 (edgePair G e).2 ↔ _
    rw [show Q.proj (edgePair G e).1 (edgePair G e).2 (A.1 (edgePair G e).1) = _
      from proj_edge G hq hp e _]
    rfl
  have hMarked (i : Fin G.edges.length) :
      (∑ z : Copies (i.val : ZMod p), if good i z.1 then (1 : ℝ) else 0) = (marked i : ℝ) := by
    rw [sum_indicator_eq_card]
    apply congrArg (Nat.cast : ℕ → ℝ)
    change _ = (Finset.univ.filter fun z =>
      good i z ∧ tag z.2 z.1 = (i.val : ZMod p)).card
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr {
      toFun := fun z => ⟨z.1.1, z.2, z.1.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.2⟩, z.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hSame : ((Q.edges.filter sat).card : ℝ) = ∑ i, (marked i : ℝ) := by
    change (((Finset.univ.map ⟨edgePair G, edgePair_injective G hp⟩).filter sat).card : ℝ) = _
    rw [Finset.filter_map, Finset.card_map, ← sum_indicator_eq_card, Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => by
      simpa only [Function.comp_apply, Function.Embedding.coeFn_mk, hSat] using hMarked i)
  have hEach (i : Fin G.edges.length) :
      (marked i : ℝ) ≤ (cnt i : ℝ)/p + (2*q:ℝ)*(p:ℝ)^5 := by
    simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using
      tag_projection_le (l (G.edges.get i).left) (r (G.edges.get i).right)
        (fun a => (G.edges.get i).projection.images[a]) (i.val : ZMod p)
  have hAll : (∑ i, (cnt i : ℝ)) ≤ (p:ℝ)^7 * G.maxSatisfied := by
    simp_rw [cnt, ← sum_indicator_eq_card]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _ : Seed p × Point p, (G.maxSatisfied : ℝ) := by
        apply Finset.sum_le_sum
        intro z _
        rw [sum_indicator_eq_card]
        have hle := countSatisfied_le G (fun u => l u z.2) (fun v => r v z.1)
        rw [countSatisfied_eq_card] at hle
        exact_mod_cast hle
      _ = _ := by
        have hsz : (Fintype.card (Seed p × Point p) : ℝ) = (p : ℝ)^7 := by
          have hsz' : Fintype.card (Seed p × Point p) = p^7 := by
            rw [Fintype.card_prod, card_seed, card_point, ← pow_add]
          exact_mod_cast hsz'
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsz]
  have hCount :
      ((Q.edges.filter sat).card : ℝ) ≤
        (p:ℝ)^6 * G.maxSatisfied + G.edges.length * (2*q:ℝ)*(p:ℝ)^5 := by
    rw [hSame]
    calc
      _ ≤ ∑ i : Fin G.edges.length, ((cnt i : ℝ)/p + (2*q:ℝ)*(p:ℝ)^5) :=
        Finset.sum_le_sum (fun i _ => hEach i)
      _ = (∑ i, (cnt i : ℝ))/p + G.edges.length * (2*q:ℝ)*(p:ℝ)^5 := by
        simp [Finset.sum_add_distrib, Finset.sum_div, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        have hpn : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'
        have h := div_le_div_of_nonneg_right hAll (Nat.cast_nonneg p : (0:ℝ) ≤ p)
        rw [pow_succ' (p:ℝ) 6, mul_assoc, mul_div_cancel_left₀ _ hpn] at h
        exact add_le_add_left h _
  have hm : (0:ℝ) < G.edges.length := Nat.cast_pos.mpr (List.length_pos_iff.mpr G.nonempty)
  have hp0 : (0:ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  change ((Q.edges.filter sat).card : ℝ) / (Q.edges.card : ℝ) ≤ _
  rw [show Q.edges.card = G.edges.length * p^6 from edge_count G hq hp, Nat.cast_mul, Nat.cast_pow]
  apply (div_le_iff₀ (mul_pos hm (pow_pos hp0 6))).mpr
  refine hCount.trans_eq ?_
  unfold Instance.value
  field_simp

end SimpleLift

end FourToOneGames

end SimpleLiftValue

section Satisfiability

set_option linter.style.haveILetI false

namespace FourToOneGames

open OAI.PerfectCompleteness.BinaryFormula

/-- The edge set must be nonempty in the exact Prove2Me definition of value one. -/
theorem value_one_iff (P : LabelCover) :
    P.val = 1 ↔ P.edges.Nonempty ∧
      ∃ A : Fin P.nL → Fin P.sizeL, ∃ B : Fin P.nR → Fin P.sizeR,
        ∀ e ∈ P.edges, P.proj e.1 e.2 (A e.1) = B e.2 := by
  classical
  let W (x : (Fin P.nL → Fin P.sizeL) × (Fin P.nR → Fin P.sizeR)) := P.valAssign x.1 x.2
  have hBound (x : (Fin P.nL → Fin P.sizeL) × (Fin P.nR → Fin P.sizeR)) : W x ≤ 1 := by
    by_cases h : P.edges.card = 0
    · simp [W, LabelCover.valAssign, h]
    · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      exact_mod_cast Finset.card_filter_le _ _
  have hBdd : BddAbove (Set.range W) := ⟨1, fun _ ⟨x, hx⟩ => hx ▸ hBound x⟩
  constructor
  · intro hv
    have hne : (Set.range W).Nonempty := by
      by_contra! h
      change sSup (Set.range W) = 1 at hv
      rw [h, Real.sSup_empty] at hv
      norm_num at hv
    have hh := hne.csSup_mem (Set.finite_range W)
    rw [show sSup (Set.range W) = 1 from hv] at hh
    obtain ⟨⟨A,B⟩, hab⟩ := hh
    have he : P.edges.card ≠ 0 := by
      intro h
      simp [W, LabelCover.valAssign, h] at hab
    refine ⟨Finset.card_pos.mp (Nat.pos_of_ne_zero he), A, B, ?_⟩
    change ((P.edges.filter fun e => P.proj e.1 e.2 (A e.1) = B e.2).card : ℝ) /
      (P.edges.card : ℝ) = 1 at hab
    have hh := (div_eq_iff (Nat.cast_ne_zero.mpr he)).mp hab
    rw [one_mul] at hh
    exact Finset.card_filter_eq_iff.mp (by exact_mod_cast hh)
  · rintro ⟨he,A,B,h⟩
    letI : Nonempty ((Fin P.nL → Fin P.sizeL) × (Fin P.nR → Fin P.sizeR)) := ⟨A,B⟩
    have hr : W (A,B) = 1 := by
      have hf := Finset.filter_eq_self.mpr h
      simp [W, LabelCover.valAssign, hf, Nat.cast_ne_zero.mpr he.card_ne_zero]
    exact le_antisymm (ciSup_le hBound) (hr ▸ le_ciSup hBdd (A,B))

private def lit (v : ℕ) (positive : Bool) : Literal := ⟨v, positive⟩

private def unitClause (l : Literal) : Clause := #v[l,l,l]

private def forbidPair (l r : ℕ) : Clause := #v[lit l false, lit r false, lit r false]

/-- Prefix variables enforce at least one selected label using clauses of length three. -/
def choiceClauses (n : ℕ) (label gate : ℕ → ℕ) : List Clause :=
  unitClause (lit (gate 0) false) ::
  unitClause (lit (gate n) true) ::
  (List.range n).map (fun i =>
    #v[lit (gate (i+1)) false, lit (gate i) true, lit (label i) true])

theorem selected_of_choiceClauses (n : ℕ) (label gate : ℕ → ℕ) (A : ℕ → Bool)
    (h : ∀ c ∈ choiceClauses n label gate, c.eval A = true) :
    ∃ i : Fin n, A (label i.val) = true := by
  have hzero : A (gate 0) = false := by
    simpa [choiceClauses, unitClause, lit, Clause.eval, Literal.eval] using
      h (unitClause (lit (gate 0) false)) (by simp [choiceClauses])
  have hn : A (gate n) = true := by
    simpa [choiceClauses, unitClause, lit, Clause.eval, Literal.eval] using
      h (unitClause (lit (gate n) true)) (by simp [choiceClauses])
  have step (i : ℕ) (hi : i < n) (hs : A (gate (i+1)) = true) :
      A (gate i) = true ∨ A (label i) = true := by
    have hc := h (#v[lit (gate (i+1)) false, lit (gate i) true, lit (label i) true])
      (by
        apply List.mem_cons_of_mem
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simpa [lit, Clause.eval, Literal.eval, hs] using hc
  have hprefix (k : ℕ) (hk : k ≤ n) (ha : A (gate k) = true) :
      ∃ i : Fin n, i.val < k ∧ A (label i.val) = true := by
    induction k with
    | zero => simp [hzero] at ha
    | succ k ih =>
      rcases step k (by omega) ha with hb | hc
      · obtain ⟨i, hi, hA⟩ := ih (by omega) hb
        exact ⟨i, by omega, hA⟩
      · exact ⟨⟨k, by omega⟩, by simp, hc⟩
  obtain ⟨i, _, hi⟩ := hprefix n le_rfl hn
  exact ⟨i, hi⟩

theorem choiceClauses_of_selected (n : ℕ) (label gate : ℕ → ℕ) (A : ℕ → Bool)
    (i : Fin n)
    (hLabel : ∀ j, A (label j) = decide (j = i.val))
    (hPrefix : ∀ j, A (gate j) = decide (i.val < j)) :
    ∀ c ∈ choiceClauses n label gate, c.eval A = true := by
  intro c hc
  simp only [choiceClauses, List.mem_cons] at hc
  rcases hc with rfl | rfl | hc
  · simp [unitClause, lit, Clause.eval, Literal.eval, hPrefix]
  · simp [unitClause, lit, Clause.eval, Literal.eval, hPrefix, i.isLt]
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    simp [lit, Clause.eval, Literal.eval, hPrefix, hLabel]
    omega

private abbrev VarKey := Bool × ℕ × Bool × ℕ

private def name (k : VarKey) : ℕ :=
  Nat.pair k.1.toNat (Nat.pair k.2.1 (Nat.pair k.2.2.1.toNat k.2.2.2))

private theorem name_injective : Function.Injective name := by
  rintro ⟨s,u,b,k⟩ ⟨s',u',b',k'⟩ h
  cases s <;> cases s' <;> cases b <;> cases b' <;> simp_all [name, Nat.pair_eq_pair]

private def vertexClauses (n d : ℕ) (side : Bool) : List Clause :=
  (List.range n).flatMap fun v => choiceClauses d (fun j => name (side,v,false,j))
    (fun j => name (side,v,true,j))

private def edgeClauses (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR) : List Clause :=
  if (u,v) ∈ P.edges then
    (List.finRange P.sizeL).flatMap fun a =>
      ((List.finRange P.sizeR).filter fun b => decide (P.proj u v a ≠ b)).map fun b =>
        forbidPair (name (false,u.val,false,a.val)) (name (true,v.val,false,b.val))
  else []

private def constraintClauses (P : LabelCover) : List Clause :=
  (List.finRange P.nL).flatMap fun u => (List.finRange P.nR).flatMap fun v => edgeClauses P u v

/-- A direct binary-3SAT formula for a perfectly satisfiable label-cover instance. -/
def satFormula (P : LabelCover) : Formula :=
  ⟨if P.edges.Nonempty then
    vertexClauses P.nL P.sizeL false ++ vertexClauses P.nR P.sizeR true ++ constraintClauses P
  else [unitClause (lit 0 true), unitClause (lit 0 false)]⟩

private theorem vertex_choice (n d : ℕ) (side : Bool) (A : ℕ → Bool)
    (h : ∀ c ∈ vertexClauses n d side, c.eval A = true) (v : Fin n) :
    ∃ j : Fin d, A (name (side,v.val,false,j.val)) = true := by
  apply selected_of_choiceClauses d (fun j => name (side,v.val,false,j))
    (fun j => name (side,v.val,true,j)) A
  intro c hc
  exact h c (List.mem_flatMap.mpr ⟨v.val, List.mem_range.mpr v.isLt, hc⟩)

private theorem vertex_sat (n d : ℕ) (side : Bool) (A : ℕ → Bool) (selected : Fin n → Fin d)
    (hLabel : ∀ (v : Fin n) j, A (name (side,v.val,false,j)) = decide (j = (selected v).val))
    (hGate : ∀ (v : Fin n) j, A (name (side,v.val,true,j)) = decide ((selected v).val < j)) :
    ∀ c ∈ vertexClauses n d side, c.eval A = true := by
  intro c hc
  obtain ⟨v,hv,hc⟩ := List.mem_flatMap.mp hc
  let w : Fin n := ⟨v,List.mem_range.mp hv⟩
  exact choiceClauses_of_selected d _ _ A (selected w) (hLabel w) (hGate w) c hc

/-- The source formula has a satisfying assignment exactly on the value-one instances. -/
theorem satFormula_satisfiable_iff (P : LabelCover) : (satFormula P).Satisfiable ↔ P.val = 1 := by
  classical
  rw [value_one_iff]
  by_cases hp : P.edges.Nonempty
  · constructor
    · rintro ⟨A,h⟩
      simp only [satFormula, if_pos hp] at h
      have hleft := vertex_choice P.nL P.sizeL false A
        (fun c hc => h c (List.mem_append_left _ (List.mem_append_left _ hc)))
      have hright := vertex_choice P.nR P.sizeR true A
        (fun c hc => h c (List.mem_append_left _ (List.mem_append_right _ hc)))
      choose L hL using hleft
      choose R hR using hright
      refine ⟨hp,L,R,?_⟩
      intro e he
      by_contra hbad
      let c := forbidPair (name (false,e.1.val,false,(L e.1).val))
        (name (true,e.2.val,false,(R e.2).val))
      have hc : c ∈ constraintClauses P := by
        apply List.mem_flatMap.mpr
        refine ⟨e.1, List.mem_finRange _, List.mem_flatMap.mpr ⟨e.2, List.mem_finRange _, ?_⟩⟩
        rw [edgeClauses, if_pos (show (e.1,e.2) ∈ P.edges from he)]
        apply List.mem_flatMap.mpr
        exact ⟨L e.1, List.mem_finRange _, List.mem_map.mpr ⟨R e.2, by simp [hbad], rfl⟩⟩
      have hf := h c (List.mem_append_right _ hc)
      simp [c, forbidPair, Clause.eval, Literal.eval, lit, hL, hR] at hf
    · rintro ⟨_,L,R,hSat⟩
      let picked (s : Bool) (v : ℕ) : ℕ :=
        if s then (if hv : v < P.nR then (R ⟨v,hv⟩).val else 0)
        else (if hv : v < P.nL then (L ⟨v,hv⟩).val else 0)
      let v (k : VarKey) : Bool := if k.2.2.1 then decide (picked k.1 k.2.1 < k.2.2.2)
        else decide (k.2.2.2 = picked k.1 k.2.1)
      let A := Function.extend name v (fun _ => false)
      have hExt (k : VarKey) : A (name k) = v k :=
        name_injective.extend_apply v (fun _ => false) k
      have hLL (u : Fin P.nL) (j : ℕ) :
          A (name (false,u.val,false,j)) = decide (j = (L u).val) := by
        rw [hExt]
        simp [v, picked, u.isLt]
      have hLR (u : Fin P.nL) (j : ℕ) :
          A (name (false,u.val,true,j)) = decide ((L u).val < j) := by
        rw [hExt]
        simp [v, picked, u.isLt]
      have hRL (u : Fin P.nR) (j : ℕ) :
          A (name (true,u.val,false,j)) = decide (j = (R u).val) := by
        rw [hExt]
        simp [v, picked, u.isLt]
      have hRR (u : Fin P.nR) (j : ℕ) :
          A (name (true,u.val,true,j)) = decide ((R u).val < j) := by
        rw [hExt]
        simp [v, picked, u.isLt]
      refine ⟨A, ?_⟩
      intro c hc
      simp only [satFormula, if_pos hp, List.mem_append] at hc
      rcases hc with (hl | hr) | he
      · exact vertex_sat P.nL P.sizeL false A L hLL hLR c hl
      · exact vertex_sat P.nR P.sizeR true A R hRL hRR c hr
      · obtain ⟨u,_,hu⟩ := List.mem_flatMap.mp he
        obtain ⟨w,_,hw⟩ := List.mem_flatMap.mp hu
        unfold edgeClauses at hw
        split_ifs at hw with hedge
        · obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hw
          obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
          have hbad := (List.mem_filter.mp hb).2
          by_cases hl : a.val = (L u).val
          · by_cases hr : b.val = (R w).val
            · have ha' : a = L u := Fin.ext hl
              have hb' : b = R w := Fin.ext hr
              simp [ha',hb',hSat (u,w) hedge] at hbad
            · simp [forbidPair, Clause.eval, Literal.eval, lit, hLL, hRL, hr]
          · simp [forbidPair, Clause.eval, Literal.eval, lit, hLL, hRL, hl]
        · exact (List.not_mem_nil hw).elim
  · simp only [satFormula, Formula.Satisfiable, hp, false_and, iff_false]
    rintro ⟨A,h⟩
    have hpos : A 0 = true := by
      simpa [unitClause, lit, Clause.eval, Literal.eval] using h (unitClause (lit 0 true)) (by simp)
    simpa [unitClause, lit, Clause.eval, Literal.eval, hpos] using
      h (unitClause (lit 0 false)) (by simp)

end FourToOneGames

end Satisfiability

section SATEncoding

set_option backward.isDefEq.respectTransparency.types false

namespace FourToOneGames

open OAI.PerfectCompleteness.BinaryFormula OAI.PerfectCompleteness.BinaryEncoding

private def frameBits (bs : List Bool) : List Bool := bs.flatMap fun b => [true,b]

private def serializeLiteral (l : Literal) : List Bool :=
  l.positive :: (frameBits l.name.bits ++ [false])

private def serializeClause (c : Clause) : List Bool :=
  serializeLiteral (c.get 0) ++ serializeLiteral (c.get 1) ++ serializeLiteral (c.get 2)

private def serializeClauses (cs : List Clause) : List Bool :=
  cs.flatMap fun c => true :: serializeClause c

/-- Binary 3SAT with the same self-delimiting syntax as the 2-to-1 reduction. -/
def serializeFormula (f : Formula) : List Bool := serializeClauses f.clauses ++ [false]

private theorem bitsValue_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => simp only [Nat.bits_append_bit _ _ h, bitsValue, ih]

private theorem parseFrame_frameBits (xs w : List Bool) :
    parseFrame (frameBits xs ++ false :: w) = some (xs,w) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    change parseFrame (true :: b :: (frameBits bs ++ false :: w)) = _
    simp [parseFrame, ih]

private theorem parseName_frameBits (n : ℕ) (w : List Bool) :
    parseName (frameBits n.bits ++ false :: w) = some (n,w) := by
  simp [parseName, parseFrame_frameBits, bitsValue_bits]

private theorem parseLiteral_serialize (l : Literal) (w : List Bool) :
    parseLiteral (serializeLiteral l ++ w) = some (l,w) := by
  cases l with
  | mk n b =>
    change parseLiteral (b :: ((frameBits n.bits ++ [false]) ++ w)) = _
    simp [parseLiteral, List.append_assoc, parseName_frameBits]

private theorem parseClause_serialize (c : Clause) (w : List Bool) :
    parseClause (serializeClause c ++ w) = some (c,w) := by
  have hc : #v[(c.get 0), (c.get 1), (c.get 2)] = c := by
    ext i hi
    interval_cases i <;> rfl
  simp [serializeClause, List.append_assoc, parseClause, parseLiteral_serialize, hc]

private theorem parseClauses_serialize (cs : List Clause) (w : List Bool)
    (fuel : ℕ) (h : cs.length < fuel) :
    parseClauses fuel (serializeClauses cs ++ false :: w) = some (cs,w) := by
  induction cs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at h
    | succ fuel => rfl
  | cons c cs ih =>
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      rw [show serializeClauses (c :: cs) =
        (true :: serializeClause c) ++ serializeClauses cs from rfl,
        List.append_assoc, List.cons_append]
      have hf : cs.length < fuel := by
        simp only [List.length_cons] at h
        omega
      simp [parseClauses, parseClause_serialize, ih fuel hf]

private theorem serializeClauses_length_ge (cs : List Clause) :
    cs.length ≤ (serializeClauses cs).length := by
  induction cs with
  | nil => simp [serializeClauses]
  | cons c cs ih =>
    simp only [serializeClauses, List.length_cons, List.flatMap_cons, List.cons_append,
      List.length_append]
    exact Nat.add_le_add_right (ih.trans (Nat.le_add_left _ _)) 1

theorem decode_serialize (f : Formula) :
    decodeFormula (serializeFormula f) = some f := by
  have h : f.clauses.length < (serializeFormula f).length + 1 := by
    have hl := serializeClauses_length_ge f.clauses
    simp [serializeFormula]
    omega
  have hparse := parseClauses_serialize f.clauses [] ((serializeFormula f).length + 1) h
  cases f
  simp [decodeFormula, serializeFormula] at hparse ⊢
  rw [hparse]
  rfl

end FourToOneGames

end SATEncoding

section Reduction

namespace FourToOneGames

open OAI.PerfectCompleteness
open Turing Turing.TM2Comp

/-- The input compiler expresses perfect satisfaction of the projection constraints as binary 3SAT. -/
def LabelCoverToBinary3SAT : Prop :=
  ∀ r₀ : ℕ, ∃ f : LabelCover → List Bool,
    Nonempty (TM2ComputableInPolyTime encodeLabelCover (id : List Bool → List Bool) f) ∧
    ∀ P, P.AlphabetBound r₀ → (BinaryLanguage.language (f P) ↔ P.val = 1)

/-- The output compiler removes parallel constraints, doubles the left labels, and incurs
at most the specified additive soundness loss. -/
def SimpleFourToOneLift : Prop :=
  ∀ (q : ℕ) (η : ℝ), 2 ≤ q → 0 < η → ∃ r : ℕ, ∃ f : Instance q → LabelCover,
    Nonempty (TM2ComputableInPolyTime Encoding.gameBits encodeLabelCover f) ∧
    ∀ G, (f G).AlphabetBound r ∧ (f G).IsDToOne 4 ∧
      (G.value = 1 → (f G).val = 1) ∧ (f G).val ≤ G.value + η

/-- Assemble the exact Prove2Me reduction from the binary 3SAT hardness theorem and
the two encoding-specific compilers. -/
theorem four_to_one_perfect_completeness_of_compilers
    (twoToOne : ∀ δ : ℚ, 0 < δ → δ < 1 → Nonempty (BinaryGapReduction δ))
    (inputCompiler : LabelCoverToBinary3SAT)
    (outputCompiler : SimpleFourToOneLift) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ r₀ : ℕ, ∃ r : ℕ,
      Nonempty (GapReduction encodeLabelCover encodeLabelCover
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val = 1)
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val ≤ s)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val = 1)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val ≤ ε)) := by
  intro ε hε
  have hb : (0 : ℝ) < min (ε / 2) 1 := lt_min (by linarith) zero_lt_one
  obtain ⟨δ, hδ, hd⟩ := exists_rat_btwn hb
  have hd0 : (0 : ℚ) < δ := by exact_mod_cast hδ
  have hd1 : δ < (1 : ℚ) := by exact_mod_cast hd.trans_le (min_le_right _ _)
  obtain ⟨R⟩ := twoToOne δ hd0 hd1
  obtain ⟨r, lift, ⟨liftTM⟩, liftSpec⟩ :=
    outputCompiler R.alphabet (ε / 2) R.alphabet_ge_two (by linarith)
  refine ⟨1/2, by norm_num, by norm_num, ?_⟩
  intro r₀
  obtain ⟨f, ⟨fTM⟩, fSpec⟩ := inputCompiler r₀
  refine ⟨r, ⟨⟨fun P => lift (R.construct (f P)), ?_, ?_, ?_⟩⟩⟩
  · exact TM2ComputableInPolyTime.comp_scratch
      (Classical.choice (TM2ComputableInPolyTime.comp_scratch fTM R.computation)) liftTM
  · intro P hp
    obtain ⟨hr, hFour, hc, _⟩ := liftSpec (R.construct (f P))
    exact ⟨hr, hFour, hc (R.completeness _ ((fSpec P hp.1).mpr hp.2))⟩
  · intro P hp
    obtain ⟨hr, hFour, _, hs⟩ := liftSpec (R.construct (f P))
    have hNot : ¬ BinaryLanguage.language (f P) := by
      intro h
      have hh := (fSpec P hp.1).mp h
      linarith [hp.2]
    refine ⟨hr, hFour, hs.trans ?_⟩
    linarith [R.soundness _ hNot, hd.trans_le (min_le_left _ _)]

end FourToOneGames

end Reduction

section ConcreteReduction

set_option linter.style.haveILetI false

namespace FourToOneGames

open OAI.PerfectCompleteness Turing

/-- The binary 3SAT input sent to the proved 2-to-1 reduction. -/
def binaryInput (P : LabelCover) : List Bool := serializeFormula (satFormula P)

theorem binaryInput_spec (P : LabelCover) :
    BinaryLanguage.language (binaryInput P) ↔ P.val = 1 := by
  unfold BinaryLanguage.language binaryInput
  rw [decode_serialize]
  constructor
  · rintro ⟨f, hf, hs⟩
    have he : satFormula P = f := Option.some.inj hf
    exact (satFormula_satisfiable_iff P).mp (he.symm ▸ hs)
  · intro hp
    exact ⟨satFormula P, rfl, (satFormula_satisfiable_iff P).mpr hp⟩

private theorem prime_exists (B m : ℕ) (hB : 0 < B) :
    ∃ p, Nat.Prime p ∧ max m B < p ∧ p ≤ 2 * max m B :=
  Nat.exists_prime_lt_and_le_two_mul (max m B) (by omega)

/-- The least prime in the interval provided by Bertrand's postulate. -/
def choosePrime (B m : ℕ) (hB : 0 < B) : ℕ :=
  Nat.find (prime_exists B m hB)

theorem choosePrime_spec (B m : ℕ) (hB : 0 < B) :
    (choosePrime B m hB).Prime ∧ max m B < choosePrime B m hB ∧
      choosePrime B m hB ≤ 2 * max m B :=
  Nat.find_spec (prime_exists B m hB)

theorem choosePrime_le_of_prime (B m : ℕ) (hB : 0 < B) {p : ℕ}
    (hp : p.Prime) (hLower : max m B < p) :
    choosePrime B m hB ≤ p := by
  by_cases hUpper : p ≤ 2 * max m B
  · exact Nat.find_min' (prime_exists B m hB) ⟨hp, hLower, hUpper⟩
  · have h := (choosePrime_spec B m hB).2.2
    omega

/-- The simple-graph game sent back to the exact label-cover encoding. -/
noncomputable def liftOutput {q : ℕ} (hq : 0 < q) (B : ℕ) (hB : 0 < B) (G : Instance q) :
    LabelCover := by
  let p := choosePrime B G.edges.length hB
  have h := choosePrime_spec B G.edges.length hB
  letI : Fact p.Prime := ⟨h.1⟩
  exact SimpleLift.game (p := p) G hq ((le_max_left _ _).trans h.2.1.le)

theorem liftOutput_spec {q : ℕ} (hq : 0 < q) (B : ℕ) (hB : 0 < B) (G : Instance q) :
    (liftOutput hq B hB G).AlphabetBound (4*q) ∧
    (liftOutput hq B hB G).IsDToOne 4 ∧
    (G.value = 1 → (liftOutput hq B hB G).val = 1) ∧
    (liftOutput hq B hB G).val ≤ G.value + (2*q : ℝ) / (choosePrime B G.edges.length hB : ℝ) := by
  let p := choosePrime B G.edges.length hB
  have h := choosePrime_spec B G.edges.length hB
  letI : Fact p.Prime := ⟨h.1⟩
  have hp : G.edges.length ≤ p := (le_max_left _ _).trans h.2.1.le
  change (SimpleLift.game G hq hp).AlphabetBound (4*q) ∧
    (SimpleLift.game G hq hp).IsDToOne 4 ∧
    (G.value = 1 → (SimpleLift.game G hq hp).val = 1) ∧
    (SimpleLift.game G hq hp).val ≤ G.value + (2*q : ℝ) / p
  have hbound : (SimpleLift.game G hq hp).AlphabetBound (4*q) := by
    change 4*q ≤ 4*q ∧ q ≤ 4*q
    exact ⟨le_rfl, by omega⟩
  exact ⟨hbound, SimpleLift.isDToOne G hq hp,
    SimpleLift.complete G hq hp, SimpleLift.sound G hq hp⟩

/-- The certified encoder and the affine lift bounds give the output compiler. -/
theorem simpleFourToOneLift_of_machine_certificate
    (liftTM : ∀ (q : ℕ) (hq : 0 < q) (B : ℕ) (hB : 0 < B),
      Nonempty (TM2ComputableInPolyTime Encoding.gameBits encodeLabelCover (liftOutput hq B hB))) :
    SimpleFourToOneLift := by
  intro q η hq hη
  have hq0 : 0 < q := by omega
  obtain ⟨b,hb⟩ := exists_nat_gt ((2*q : ℝ) / η)
  let B := b+1
  have hB : 0 < B := Nat.succ_pos b
  refine ⟨4*q, liftOutput hq0 B hB, liftTM q hq0 B hB, ?_⟩
  intro G
  obtain ⟨hr,hfour,hc,hs⟩ := liftOutput_spec hq0 B hB G
  have hPrime := choosePrime_spec B G.edges.length hB
  have hbp : b < choosePrime B G.edges.length hB :=
    (Nat.lt_succ_self b).trans_le ((le_max_right _ _).trans hPrime.2.1.le)
  have hPos : (0 : ℝ) < (choosePrime B G.edges.length hB : ℕ) :=
    Nat.cast_pos.mpr hPrime.1.pos
  have hε : (2*q : ℝ) / (choosePrime B G.edges.length hB : ℝ) ≤ η := by
    apply (div_le_iff₀ hPos).mpr
    have hl := (div_lt_iff₀ hη).mp (hb.trans (Nat.cast_lt.mpr hbp))
    simpa only [mul_comm] using hl.le
  exact ⟨hr,hfour,hc,hs.trans (add_le_add_right hε _)⟩

/-- Combine the two encoding-specific certificates with the binary 3SAT reduction. -/
theorem four_to_one_perfect_completeness_of_machine_certificates
    (twoToOne : ∀ δ : ℚ, 0 < δ → δ < 1 → Nonempty (BinaryGapReduction δ))
    (satTM : Nonempty (TM2ComputableInPolyTime encodeLabelCover (id : List Bool → List Bool) binaryInput))
    (liftTM : ∀ (q : ℕ) (hq : 0 < q) (B : ℕ) (hB : 0 < B),
      Nonempty (TM2ComputableInPolyTime Encoding.gameBits encodeLabelCover (liftOutput hq B hB))) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ r₀ : ℕ, ∃ r : ℕ,
      Nonempty (GapReduction encodeLabelCover encodeLabelCover
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val = 1)
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val ≤ s)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val = 1)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val ≤ ε)) :=
  four_to_one_perfect_completeness_of_compilers twoToOne
    (fun _ => ⟨binaryInput, satTM, fun P _ => binaryInput_spec P⟩)
    (simpleFourToOneLift_of_machine_certificate liftTM)

end FourToOneGames

end ConcreteReduction

end

/- LiftOutputWords -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines

private theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intros
  simp

private theorem ascendingWords_fin {A : Type} {n : ℕ} (f : ℕ → List A) (g : Fin n → List A)
    (he : ∀ i, f i.val = g i) :
    ascendingWords f n = (List.finRange n).flatMap g := by
  rw [ascendingWords, ← finRange_values n, List.flatMap_map]
  simp only [he]

/-- A natural-number index for one entry of the adjacency matrix. -/
def adjacencyEntry (P : LabelCover) (i j : ℕ) : List Bool :=
  if hi : i < P.nL then
    if hj : j < P.nR then [decide ((⟨i,hi⟩,⟨j,hj⟩) ∈ P.edges)] else []
  else []

/-- A natural-number index for one entry of the dense unary projection table. -/
def projectionEntry (P : LabelCover) (i j a : ℕ) : List Bool :=
  if hi : i < P.nL then
    if hj : j < P.nR then
      if ha : a < P.sizeL then unary true false (P.proj ⟨i,hi⟩ ⟨j,hj⟩ ⟨a,ha⟩).val else []
    else []
  else []

theorem rectangle_adjacency (P : LabelCover) :
    rectangleWords (adjacencyEntry P) P.nL P.nR = adjacencyBits P := by
  unfold rectangleWords adjacencyBits
  apply ascendingWords_fin
  intro i
  rw [List.map_eq_flatMap]
  apply ascendingWords_fin
  intro j
  simp [adjacencyEntry, i.isLt, j.isLt]

theorem rectangle_projection (P : LabelCover) :
    rectangleWords (fun i j => ascendingWords (projectionEntry P i j) P.sizeL) P.nL P.nR =
      (projectionWords P).flatMap (unary true false) := by
  unfold rectangleWords projectionWords
  simp only [List.flatMap_assoc]
  apply ascendingWords_fin
  intro i
  apply ascendingWords_fin
  intro j
  change ascendingWords (projectionEntry P i.val j.val) P.sizeL =
    ((List.finRange P.sizeL).map fun a => (P.proj i j a).val).flatMap (unary true false)
  rw [List.flatMap_map]
  apply ascendingWords_fin
  intro a
  simp [projectionEntry, i.isLt, j.isLt, a.isLt]

theorem encodeLabelCover_rectangles (P : LabelCover) :
    encodeLabelCover P =
      ([P.nL, P.nR, P.sizeL, P.sizeR].flatMap (unary true false)) ++
        rectangleWords (adjacencyEntry P) P.nL P.nR ++
        rectangleWords (fun i j => ascendingWords (projectionEntry P i j) P.sizeL) P.nL P.nR := by
  rw [rectangle_adjacency, rectangle_projection, labelCover_input_layout]

namespace LiftOutput

open OAI.PerfectCompleteness SimpleLift

/-- The affine tag written entirely in the natural arithmetic used by the machine. -/
def ordinal (p u v : ℕ) : ℕ :=
  let x := u % p^3
  let s := v % p^4
  let y := s / p
  (s%p + (x/(p*p))*(y/(p*p)) + (x%(p*p)/p)*(y%(p*p)/p) +
    (x%(p*p)%p)*(y%(p*p)%p)) % p

theorem ordinal_correct {p q : ℕ} [Fact (Nat.Prime p)] (G : Instance q)
    (u : Fin (G.leftVertices*p^3)) (v : Fin (G.rightVertices*p^4)) :
    edgeOrdinal G u v = ordinal p u.val v.val := by
  obtain ⟨h0, h1, h2⟩ := leftIndex_symm_coordinates G u
  obtain ⟨h3, h4, h5, h6⟩ := rightIndex_symm_coordinates G v
  rw [edgeOrdinal, tag_val_natural, h0, h1, h2, h3, h4, h5, h6]
  rfl

def edgeBit {q : ℕ} (G : Instance q) (p u v : ℕ) : Bool :=
  if h : ordinal p u v < G.edges.length then
    let e := G.edges.get ⟨ordinal p u v,h⟩
    decide (e.left.val = u/p^3 ∧ e.right.val = v/p^4)
  else false

def projectionIndex {q : ℕ} (G : Instance q) (p u v a : ℕ) : ℕ :=
  if h : ordinal p u v < G.edges.length then
    if ha : a/2 < 2*q then
      ((G.edges.get ⟨ordinal p u v,h⟩).projection.images.get ⟨a/2,ha⟩).val
    else 0
  else 0

theorem edgeBit_correct {p q : ℕ} [Fact (Nat.Prime p)] (G : Instance q)
    (hq : 0 < q) (hp : G.edges.length ≤ p)
    (u : Fin (G.leftVertices*p^3)) (v : Fin (G.rightVertices*p^4)) :
    edgeBit G p u.val v.val = decide ((u,v) ∈ (game G hq hp).edges) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, game_edge_iff]
  unfold edgeBit
  rw [← ordinal_correct G u v]
  by_cases h : edgeOrdinal G u v < G.edges.length
  · simp [h, Fin.ext_iff, leftIndex_symm_vertex, rightIndex_symm_vertex]
  · simp [h]

theorem projectionIndex_correct {p q : ℕ} [Fact (Nat.Prime p)] (G : Instance q)
    (hq : 0 < q) (hp : G.edges.length ≤ p)
    (u : Fin (G.leftVertices*p^3)) (v : Fin (G.rightVertices*p^4)) (a : Fin (4*q)) :
    projectionIndex G p u.val v.val a.val = ((game G hq hp).proj u v a).val := by
  rw [game_proj_eq]
  unfold projectionIndex
  rw [← ordinal_correct G u v]
  by_cases h : edgeOrdinal G u v < G.edges.length
  · have ha : a.val/2 < 2*q := by
      rw [← labelIndex_symm_base a]
      exact ((labelIndex q).symm a).1.isLt
    have hi : (⟨a.val/2,ha⟩ : Fin (2*q)) = ((labelIndex q).symm a).1 :=
      Fin.ext (labelIndex_symm_base a).symm
    simp [h, ha, hi]
    rfl
  · simp [h]

private theorem topDigit (p x : ℕ) :
    x % p^3 / (p*p) = x/(p*p)%p := by
  rw [show p^3 = (p*p)*p by ring, Nat.mod_mul_right_div_self]

private theorem middleDigit (p x : ℕ) :
    x % p^3 % (p*p) / p = x/p%p := by
  rw [show p^3 = (p*p)*p by ring, Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self]

private theorem lowDigit (p x : ℕ) :
    x % p^3 % (p*p) % p = x%p := by
  rw [show p^3 = (p*p)*p by ring, Nat.mod_mul_right_mod, Nat.mod_mul_left_mod]

/-- The three copy coordinates are successive remainders in base `p`. -/
theorem ordinal_divisions (p u v : ℕ) :
    ordinal p u v =
      (v%p + (u/p/p%p)*(v/p/p/p%p) + (u/p%p)*(v/p/p%p) + (u%p)*(v/p%p)) % p := by
  have hpow : p^4 = p*p^3 := by ring
  have hs : v % p^4 / p = (v/p) % p^3 := by rw [hpow, Nat.mod_mul_right_div_self]
  have ho : v % p^4 % p = v % p := by rw [hpow, Nat.mod_mul_right_mod]
  simp only [ordinal, hs, ho, topDigit, middleDigit, lowDigit, Nat.div_div_eq_div_mul, Nat.mul_assoc]

private theorem ascending_congr {A : Type} (n : ℕ) {a b : ℕ → List A}
    (h : ∀ i < n, a i = b i) : ascendingWords a n = ascendingWords b n :=
  List.flatMap_congr (fun i hi => h i (List.mem_range.mp hi))

theorem liftedEncoding_words {p q : ℕ} [Fact (Nat.Prime p)] (G : Instance q)
    (hq : 0 < q) (hp : G.edges.length ≤ p) :
    encodeLabelCover (game G hq hp) =
      ([G.leftVertices*p^3, G.rightVertices*p^4, 4*q, q].flatMap (unary true false)) ++
        rectangleWords (fun i j => [edgeBit G p i j]) (G.leftVertices*p^3) (G.rightVertices*p^4) ++
        rectangleWords (fun i j => ascendingWords (fun a => unary true false
          (projectionIndex G p i j a)) (4*q)) (G.leftVertices*p^3) (G.rightVertices*p^4) := by
  let P := game G hq hp
  have ha : rectangleWords (adjacencyEntry P) P.nL P.nR =
      rectangleWords (fun i j => [edgeBit G p i j]) P.nL P.nR := by
    unfold rectangleWords
    apply ascending_congr
    intro i hi
    apply ascending_congr
    intro j hj
    simp only [adjacencyEntry, dif_pos hi, dif_pos hj]
    exact congrArg (fun b => [b]) (edgeBit_correct G hq hp ⟨i,hi⟩ ⟨j,hj⟩).symm
  have hproj : rectangleWords (fun i j => ascendingWords (projectionEntry P i j) P.sizeL) P.nL P.nR =
      rectangleWords (fun i j => ascendingWords (fun a => unary true false
        (projectionIndex G p i j a)) P.sizeL) P.nL P.nR := by
    unfold rectangleWords
    apply ascending_congr
    intro i hi
    apply ascending_congr
    intro j hj
    apply ascending_congr
    intro a haa
    simp only [projectionEntry, dif_pos hi, dif_pos hj, dif_pos haa]
    exact congrArg (unary true false) (projectionIndex_correct G hq hp ⟨i,hi⟩ ⟨j,hj⟩ ⟨a,haa⟩).symm
  rw [encodeLabelCover_rectangles P, ha, hproj]

end LiftOutput

end FourToOneGames.WordMachines

end

/- LiftTagMachine -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines

open CookPvsNP

/-- Append the unary product on the selected output tape, leaving the operands unchanged. -/
theorem multiplyOn_exec {K A : Type} [DecidableEq K] (e : Fin 5 ↪ K) (s : K → List A)
    (token : A) (a b : ℕ)
    (ha : s (e 0) = List.replicate a token) (hb : s (e 1) = List.replicate b token)
    (h3 : s (e 3) = []) (h4 : s (e 4) = []) :
    (onPorts e multiply).Exec s
      (Function.update s (e 2) (List.replicate (a*b) token ++ s (e 2))) ((6*a+13)*b+5) := by
  refine onPorts_exec e (multiply_exec token a b (s (e 2))) ?_ ?_ ?_
  · intro k
    fin_cases k <;> simp [ha, hb, h3, h4]
  · intro k
    fin_cases k <;> simp [e.injective.eq_iff, ha, hb, h3, h4]
  · intro k hk
    simp only [Function.update_of_ne (Ne.symm (hk 2))]

namespace LiftOutput

open Radix

/-- Left digits are in increasing significance. The first right digit is the offset. -/
def tagNumerator (x : Fin 3 → ℕ) (y : Fin 4 → ℕ) : ℕ :=
  y 0 + x 2*y 3 + x 1*y 2 + x 0*y 1

theorem ordinal_decoded (p u v : ℕ) :
    ordinal p u v = tagNumerator (fun i => digits u p 3 (i.castLE (by decide)))
      (digits v p 4) % p := by
  simp [ordinal_divisions, tagNumerator, digits, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_assoc]

def tagFrame (p : ℕ) (x : Fin 3 → ℕ) (y : Fin 4 → ℕ) (acc result : ℕ) : Fin 13 → List Bool :=
  ![List.replicate p true, List.replicate (x 0) true, List.replicate (x 1) true,
    List.replicate (x 2) true, List.replicate (y 0) true, List.replicate (y 1) true,
    List.replicate (y 2) true, List.replicate (y 3) true,
    List.replicate acc true, List.replicate result true, [], [], []]

private def termPorts : Fin 3 → Fin 5 ↪ Fin 13 := ![
  ⟨![1,5,8,10,11], by decide⟩, ⟨![2,6,8,10,11], by decide⟩,
  ⟨![3,7,8,10,11], by decide⟩]

private def modPorts : Fin 6 ↪ Fin 13 := ⟨![8,0,10,11,9,12], by decide⟩

/-- Compute the tag from the seven copy digits, preserving the decoded coordinates. -/
noncomputable def tagMachine : StackProg (Fin 13) Bool :=
  .seq (copyProg 4 8 10) (.seq (onPorts (termPorts 2) multiply)
    (.seq (onPorts (termPorts 1) multiply) (.seq (onPorts (termPorts 0) multiply)
      (.seq (onPorts modPorts extract) (clearProg 8)))))

private theorem copyOffset_exec (p : ℕ) (x : Fin 3 → ℕ) (y : Fin 4 → ℕ) :
    (copyProg (4 : Fin 13) 8 10).Exec (tagFrame p x y 0 0) (tagFrame p x y (y 0) 0)
      (6*y 0+3) := by
  convert stack_copy (4 : Fin 13) 8 10 (by decide) (by decide) (by decide)
    (tagFrame p x y 0 0) rfl using 1 <;>
    first | rfl |
      exact funext (fun k => by fin_cases k <;> simp [tagFrame]) |
      solve | simp [tagFrame]

private theorem addTerm_exec (p : ℕ) (x : Fin 3 → ℕ) (y : Fin 4 → ℕ)
    (acc : ℕ) (i : Fin 3) :
    (onPorts (termPorts i) multiply).Exec (tagFrame p x y acc 0)
      (tagFrame p x y (acc + x i * y i.succ) 0) ((6*x i+13)*y i.succ+5) := by
  let s := tagFrame p x y acc 0
  have h := multiplyOn_exec (termPorts i) s true (x i) (y i.succ)
    (by fin_cases i <;> rfl) (by fin_cases i <;> rfl)
    (by fin_cases i <;> rfl) (by fin_cases i <;> rfl)
  convert h using 1
  exact funext (fun k => by fin_cases i <;> fin_cases k <;>
    simp [s, tagFrame, termPorts, Nat.add_comm])

def tagBound (p : ℕ) : ℕ :=
  let cap := p+3*(p*p)
  6*p+3*((6*p+13)*p+5) + extractBound cap p + 3*cap + 9

theorem tagMachine_exec (p : ℕ) (hp : 0 < p) (x : Fin 3 → ℕ) (y : Fin 4 → ℕ)
    (hx : ∀ i, x i < p) (hy : ∀ i, y i < p) :
    ∃ t, tagMachine.Exec (tagFrame p x y 0 0)
      (tagFrame p x y 0 (tagNumerator x y % p)) t ∧ t ≤ tagBound p := by
  let n := tagNumerator x y
  let s := tagFrame p x y n 0
  obtain ⟨u, hu, huB⟩ := extractOn_exec modPorts s n p hp rfl rfl rfl rfl rfl rfl
  have htag : (onPorts modPorts extract).Exec s (tagFrame p x y (n/p) (n%p)) u := by
    convert hu using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have hclear : (clearProg (8 : Fin 13)).Exec (tagFrame p x y (n/p) (n%p))
      (tagFrame p x y 0 (n%p)) (3*(n/p)+1) := by
    convert clear_exec (8 : Fin 13) (tagFrame p x y (n/p) (n%p)) using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl) |
        solve | simp [tagFrame]
  have hrun := (copyOffset_exec p x y).seq ((addTerm_exec p x y (y 0) 2).seq
    ((addTerm_exec p x y (y 0 + x 2*y 3) 1).seq
      ((addTerm_exec p x y (y 0 + x 2*y 3 + x 1*y 2) 0).seq (htag.seq hclear))))
  refine ⟨_, hrun, ?_⟩
  have hp0 (i : Fin 3) : x i*y i.succ ≤ p*p := Nat.mul_le_mul (hx i).le (hy i.succ).le
  have hn : n ≤ p+3*(p*p) := by
    have h0 := hp0 0
    have h1 := hp0 1
    have h2 := hp0 2
    have h3 := hy 0
    change y 0 + x 2*y 3 + x 1*y 2 + x 0*y 1 ≤ p+3*(p*p)
    change x 0*y 1 ≤ p*p at h0
    change x 1*y 2 ≤ p*p at h1
    change x 2*y 3 ≤ p*p at h2
    omega
  have hm : extractBound n p ≤ extractBound (p+3*(p*p)) p := by
    unfold extractBound
    gcongr
  have hq := (Nat.div_le_self n p).trans hn
  have hterms (i : Fin 3) : (6*x i+13)*y i.succ+5 ≤ (6*p+13)*p+5 := by
    have h1 := (hx i).le
    have h2 := (hy i.succ).le
    gcongr
  have h0 := hterms 0
  have h1 := hterms 1
  have h2 := hterms 2
  have h3 := hy 0
  simp only [tagBound]
  omega

end LiftOutput

end FourToOneGames.WordMachines

end

/- PrimeScan -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.PrimeScan

open CookPvsNP UnaryDivision

private def ports : Fin 8 ↪ Fin 9 := ⟨Fin.castLE (by decide), Fin.castLE_injective (by decide)⟩

def store (n d count : ℕ) (out : List Bool) : Fin 9 → List Bool :=
  Fin.lastCases (List.replicate count true) (trialStore n d out)

private def advance : StackProg (Fin 9) Bool :=
  .act fun _ k => if k = 1 ∨ k = 8 then .pop else .keep

/-- Visit successive positive divisors in descending order and record the trial results. -/
noncomputable def scan : StackProg (Fin 9) Bool :=
  .loop (fun h => (h 8).isSome) (.seq (onPorts ports trialDivisor) advance)

def results (n d : ℕ) : ℕ → List Bool
  | 0 => []
  | c+1 => results n (d-1) c ++ [decide (d ∣ n)]

def trialBound (n d : ℕ) : ℕ := 12*(d+1)*(n+1)+9*n+3*d+22

private theorem trialBound_mono (n : ℕ) {d e : ℕ} (h : d ≤ e) :
    trialBound n d ≤ trialBound n e := by
  unfold trialBound
  gcongr

private theorem trialOnPorts (n d c : ℕ) (out : List Bool) (hd : 0 < d) :
    ∃ t, (onPorts ports trialDivisor).Exec (store n d c out)
      (store n d c (decide (d ∣ n) :: out)) t ∧ t+4 ≤ trialBound n d := by
  obtain ⟨t, ht, hb⟩ := trialDivisor_exec n d hd out
  refine ⟨t, onPorts_exec ports ht ?_ ?_ ?_, by simp only [trialBound]; omega⟩
  · intro k
    exact Fin.lastCases_castSucc k
  · intro k
    exact Fin.lastCases_castSucc k
  · intro k h
    refine Fin.lastCases ?_ (fun i => ?_) k h
    · intro _
      simp only [store, Fin.lastCases_last]
    · intro hi
      exact (hi i rfl).elim

private theorem advance_exec (n d c : ℕ) (out : List Bool) :
    advance.Exec (store n d (c+1) out) (store n (d-1) c out) 1 := by
  unfold advance
  convert StackProg.Exec.act _ (store n d (c+1) out) using 1
  exact funext (fun k => by
    fin_cases k <;> first | rfl | (cases d <;> rfl))

theorem scan_exec (n d c : ℕ) (hc : c ≤ d) (out : List Bool) :
    ∃ t, scan.Exec (store n d c out) (store n (d-c) 0 (results n d c ++ out)) t ∧
      t ≤ trialBound n d * c + 1 := by
  induction c generalizing d out with
  | zero =>
      exact ⟨1, StackProg.Exec.loopFalse rfl, by simp⟩
  | succ c ih =>
      obtain ⟨t, ht, hb⟩ := trialOnPorts n d (c+1) out (by omega)
      have ha := advance_exec n d c (decide (d ∣ n) :: out)
      obtain ⟨u, hu, hub⟩ := ih (d-1) (by omega) (decide (d ∣ n) :: out)
      have hrun := StackProg.Exec.loopTrue
        (test := fun h => (h (8 : Fin 9)).isSome) rfl (ht.seq ha) hu
      have hindex : d-1-c = d-(c+1) := by omega
      refine ⟨1 + (t+1+1) + 1 + u, ?_, ?_⟩
      · simpa only [scan, results, hindex, List.append_assoc, List.singleton_append] using hrun
      · have hub' := hub.trans (Nat.add_le_add_right
          (Nat.mul_le_mul_right c (trialBound_mono n (Nat.sub_le d 1))) 1)
        rw [Nat.mul_succ]
        omega

theorem results_any (n d c : ℕ) (h : c ≤ d) :
    (results n d c).any id = true ↔ ∃ k, d-c < k ∧ k ≤ d ∧ k ∣ n := by
  induction c generalizing d with
  | zero =>
      simp [results]
      intro k hk hle
      omega
  | succ c ih =>
      have hindex : d-1-c = d-(c+1) := by omega
      have hih := ih (d-1) (by omega)
      simp only [results, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
        id_eq, Bool.or_eq_true, decide_eq_true_eq, hih, hindex]
      constructor
      · rintro (⟨k, hk, hb, hd⟩ | hd)
        · exact ⟨k, hk, by omega, hd⟩
        · exact ⟨d, by omega, le_rfl, hd⟩
      · rintro ⟨k, hk, hb, hd⟩
        by_cases he : k = d
        · exact Or.inr (he ▸ hd)
        · exact Or.inl ⟨k, hk, by omega, hd⟩

theorem results_length (n d c : ℕ) : (results n d c).length = c := by
  induction c generalizing d with
  | zero => rfl
  | succ c ih => simp [results, ih]

/-- For a candidate at least two, a true trial bit detects compositeness. -/
theorem composite_flag (n : ℕ) (hn : 2 ≤ n) :
    (results n (n-1) (n-2)).any id = decide (¬n.Prime) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, results_any n (n-1) (n-2) (by omega)]
  constructor
  · rintro ⟨k, hlo, hhi, hdvd⟩ hp
    exact (Nat.prime_def_lt'.mp hp).2 k (by omega) (by omega) hdvd
  · intro hp
    by_contra h
    apply hp
    refine Nat.prime_def_lt'.mpr ⟨hn, ?_⟩
    intro k hlo hhi hdvd
    exact h ⟨k, by omega, by omega, hdvd⟩

private def scanPorts : Fin 9 ↪ Fin 10 := ⟨Fin.castLE (by decide), Fin.castLE_injective (by decide)⟩
private def flagPorts : Fin 4 ↪ Fin 10 := ⟨![7,9,2,3], by decide⟩

def candidateStore (n d c : ℕ) (trials out : List Bool) : Fin 10 → List Bool :=
  Fin.lastCases out (store n d c trials)

/-- Test one candidate using its configured divisor and countdown tapes. -/
noncomputable def testCandidate : StackProg (Fin 10) Bool :=
  .seq (onPorts scanPorts scan) (onPorts flagPorts anyTrue)

theorem testCandidate_exec (n : ℕ) (hn : 2 ≤ n) (out : List Bool) :
    ∃ t, testCandidate.Exec (candidateStore n (n-1) (n-2) [] out)
      (candidateStore n 1 0 (results n (n-1) (n-2)) (decide (¬n.Prime) :: out)) t ∧
      t ≤ trialBound n (n-1) * (n-2) + 9*(n-2) + 11 := by
  let xs := results n (n-1) (n-2)
  let composite := decide (¬n.Prime)
  let src := candidateStore n (n-1) (n-2) [] out
  let mid := candidateStore n 1 0 xs out
  let flagged := candidateStore n 1 0 xs (composite :: out)
  obtain ⟨t, ht, hb⟩ := scan_exec n (n-1) (n-2) (by omega) []
  have hsub : n-1-(n-2) = 1 := by omega
  rw [hsub, List.append_nil] at ht
  have hscan : (onPorts scanPorts scan).Exec src mid t := by
    refine onPorts_exec scanPorts ht ?_ ?_ ?_
    · intro k
      exact Fin.lastCases_castSucc k
    · intro k
      exact Fin.lastCases_castSucc k
    · intro k hk
      refine Fin.lastCases ?_ (fun i => ?_) k hk
      · intro _
        simp only [src, mid, candidateStore, Fin.lastCases_last]
      · intro hi
        exact (hi i rfl).elim
  obtain ⟨u, hu, huB⟩ := anyTrue_exec xs out
  have hu' : anyTrue.Exec ![xs, out, [], []] ![xs, composite :: out, [], []] u := by
    simpa only [xs, composite, composite_flag n hn] using hu
  have hflag : (onPorts flagPorts anyTrue).Exec mid flagged u := by
    refine onPorts_exec flagPorts hu' ?_ ?_ ?_
    · intro k
      fin_cases k <;> rfl
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      refine Fin.lastCases ?_ (fun i => ?_) k hk
      · intro hi
        exact (hi 1 rfl).elim
      · intro _
        simp only [mid, flagged, candidateStore, Fin.lastCases_castSucc]
  refine ⟨_, hscan.seq hflag, ?_⟩
  have hlen : xs.length = n-2 := results_length n (n-1) (n-2)
  omega

end FourToOneGames.WordMachines.PrimeScan

end

/- PrimePreparation -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.PrimeScan

open CookPvsNP UnaryDivision

private def distribute : StackProg (Fin 9) Bool :=
  transferProg 0 (fun k => decide (k = 1 ∨ k = 6 ∨ k = 8))

private def restore : StackProg (Fin 9) Bool :=
  transferProg 6 (fun k => decide (k = 0))

private def moveBounds : StackProg (Fin 9) Bool :=
  .act (fun _ k => if k = 1 ∨ k = 8 then .pop else .keep)

def prepare : StackProg (Fin 9) Bool :=
  .seq distribute (.seq restore (.seq moveBounds (popProg 8)))

private theorem asVector (n d c : ℕ) (out : List Bool) :
    store n d c out =
      ![List.replicate n true, List.replicate d true, [], [], [], [], [],
        out, List.replicate c true] := by
  funext k
  fin_cases k <;> rfl

theorem prepare_exec (n : ℕ) (hn : 2 ≤ n) :
    prepare.Exec (store n 0 0 []) (store n (n-1) (n-2) []) (6*n+7) := by
  let bits := List.replicate n true
  let s0 := store n 0 0 []
  let s1 : Fin 9 → List Bool := ![[], bits, [], [], [], [], bits, [], bits]
  let s2 := store n n n []
  let s3 := store n (n-1) (n-1) []
  let s4 := store n (n-1) (n-2) []
  have hcopy : distribute.Exec s0 s1 (3*n+1) := by
    unfold distribute
    convert stack_transfer (0 : Fin 9) (fun k => decide (k = 1 ∨ k = 6 ∨ k = 8))
      s0 using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;>
        simp [s0, s1, asVector, bits, transferStore]) |
        solve | simp [s0, asVector]
  have hrestore : restore.Exec s1 s2 (3*n+1) := by
    unfold restore
    convert stack_transfer (6 : Fin 9) (fun k => decide (k = 0)) s1 using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;>
        simp [s1, s2, asVector, bits, transferStore]) |
        solve | simp [s1, bits]
  have hmove : moveBounds.Exec s2 s3 1 := by
    unfold moveBounds
    convert StackProg.Exec.act _ s2 using 1
    exact funext (fun k => by fin_cases k <;>
      simp [s2, s3, asVector, StackProg.applyAct, StackAct.apply, List.tail_replicate])
  have hpop : (popProg (8 : Fin 9)).Exec s3 s4 1 := by
    convert pop_exec (8 : Fin 9) s3 using 1
    have hn' : n-1-1 = n-2 := by omega
    exact funext (fun k => by fin_cases k <;>
      simp [s3, s4, asVector, List.tail_replicate, hn'])
  convert hcopy.seq (hrestore.seq (hmove.seq hpop)) using 1 <;> first | rfl | omega

private def prepPorts : Fin 9 ↪ Fin 10 := ⟨Fin.castLE (by decide), Fin.castLE_injective (by decide)⟩

/-- Initialize a fresh unary candidate, then test all of its proper divisors. -/
noncomputable def testUnary : StackProg (Fin 10) Bool :=
  .seq (onPorts prepPorts prepare) testCandidate

theorem candidateStore_eq (n d c : ℕ) (trials out : List Bool) :
    candidateStore n d c trials out =
      ![List.replicate n true, List.replicate d true, [], [], [], [], [],
        trials, List.replicate c true, out] := by
  funext k
  fin_cases k <;> rfl

theorem testUnary_exec (n : ℕ) (hn : 2 ≤ n) :
    ∃ t, testUnary.Exec (candidateStore n 0 0 [] [])
      (candidateStore n 1 0 (results n (n-1) (n-2)) [decide (¬n.Prime)]) t ∧
      t ≤ trialBound n (n-1) * (n-2) + 9*(n-2) + 6*n + 19 := by
  have hp : (onPorts prepPorts prepare).Exec (candidateStore n 0 0 [] [])
      (candidateStore n (n-1) (n-2) [] []) (6*n+7) := by
    refine onPorts_exec prepPorts (prepare_exec n hn) ?_ ?_ ?_
    · intro k
      exact Fin.lastCases_castSucc k
    · intro k
      exact Fin.lastCases_castSucc k
    · intro k hk
      refine Fin.lastCases ?_ (fun i => ?_) k hk
      · intro _
        simp only [candidateStore, Fin.lastCases_last]
      · intro hi
        exact (hi i rfl).elim
  obtain ⟨v, hv, hb⟩ := testCandidate_exec n hn []
  exact ⟨_, hp.seq hv, by omega⟩

abbrev Candidate := {n : ℕ // 2 ≤ n}

def candidateBits (n : Candidate) : List Bool := List.replicate n.val true

def composite (n : Candidate) : Bool := decide (¬n.val.Prime)

open Polynomial in
private noncomputable def primeBudget : Polynomial ℕ :=
  (12*(X+1)*(X+1)+9*X+3*X+22)*X + 15*X+19

/-- A polynomial-time TM2 certificate for testing a unary candidate. -/
noncomputable def composite_polytime :
    Turing.TM2ComputableInPolyTime candidateBits (fun b => [b]) composite :=
  StackTM2Time.programPolytime candidateBits (fun b => [b]) composite testUnary 0 9 primeBudget
    (fun P => by
      let n := P.val
      let s0 := candidateStore n 0 0 [] []
      let s2 := candidateStore n 1 0 (results n (n-1) (n-2)) [composite P]
      have hinit : (testUnary.machine.init 0 (candidateBits P)).store = s0 := by
        funext k
        rw [show s0 = _ from candidateStore_eq n 0 0 [] []]
        fin_cases k <;> rfl
      obtain ⟨v, hv, hb⟩ := testUnary_exec n P.property
      rw [← (show _ = candidateStore n 0 0 [] [] from hinit)] at hv
      refine ⟨s2, v, hv, rfl, ?_⟩
      have hm : trialBound n (n-1) ≤ trialBound n n := by
        unfold trialBound
        gcongr <;> omega
      have ht := Nat.mul_le_mul hm (Nat.sub_le n 2)
      have hlen : (candidateBits P).length = n := List.length_replicate
      simp only [primeBudget, hlen, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
      unfold trialBound at ht hb
      omega)

end FourToOneGames.WordMachines.PrimeScan

end

/- PrimeSearch -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.PrimeScan

open CookPvsNP

def checkedStore (n : ℕ) : Fin 10 → List Bool :=
  candidateStore n 0 0 [] [decide (¬n.Prime)]

/-- Test the current candidate and empty the work tapes used by its divisor scan. -/
noncomputable def checkCurrent : StackProg (Fin 10) Bool :=
  .seq testUnary (.seq (clearProg 1) (clearProg 7))

private def guard (h : Fin 10 → Option Bool) : Bool := h 9 == some true

private def incrementCandidate : StackProg (Fin 10) Bool :=
  .act (fun _ k => if k = 0 then .push true else if k = 9 then .pop else .keep)

/-- Continue testing consecutive candidates until a prime is found. -/
noncomputable def searchLoop : StackProg (Fin 10) Bool :=
  .loop guard (.seq incrementCandidate checkCurrent)

def stepBound (n : ℕ) : ℕ := trialBound n n * n + 20*n + 32

private theorem checkCurrent_exec (n p : ℕ) (hn : 2 ≤ n) (hupper : n ≤ p) :
    ∃ t, checkCurrent.Exec (candidateStore n 0 0 [] []) (checkedStore n) t ∧
      t + 4 ≤ stepBound p := by
  obtain ⟨t, ht, hb⟩ := testUnary_exec n hn
  let trials := results n (n-1) (n-2)
  let flag := [decide (¬n.Prime)]
  let s1 := candidateStore n 1 0 trials flag
  let s2 := candidateStore n 0 0 trials flag
  have h1 : (clearProg (1 : Fin 10)).Exec s1 s2 4 := by
    convert clear_exec (1 : Fin 10) s1 using 1 <;>
      first | rfl | exact funext (fun k => by
        simp only [s1, s2, candidateStore_eq]
        fin_cases k <;> rfl)
  have h2 : (clearProg (7 : Fin 10)).Exec s2 (checkedStore n) (3*trials.length+1) := by
    convert clear_exec (7 : Fin 10) s2 using 1 <;>
      first | rfl | exact funext (fun k => by
        simp only [s2, checkedStore, candidateStore_eq, flag]
        fin_cases k <;> rfl)
  refine ⟨_, ht.seq (h1.seq h2), ?_⟩
  have hmono : trialBound n (n-1) ≤ trialBound p p := by
    unfold trialBound
    gcongr <;> omega
  have hprod := Nat.mul_le_mul hmono (show n-2 ≤ p by omega)
  rw [show trials.length = n-2 from results_length n (n-1) (n-2), stepBound]
  omega

private theorem incrementCandidate_exec (n : ℕ) (flag : List Bool) :
    incrementCandidate.Exec (candidateStore n 0 0 [] flag)
      (candidateStore (n+1) 0 0 [] flag.tail) 1 := by
  unfold incrementCandidate
  convert StackProg.Exec.act _ (candidateStore n 0 0 [] flag) using 1
  exact funext (fun k => by
    simp only [candidateStore_eq]
    fin_cases k <;> rfl)

theorem searchLoop_exec (p n : ℕ) (hn : 2 ≤ n) (hnp : n ≤ p) (hp : p.Prime)
    (hfirst : ∀ i, n ≤ i → i < p → ¬i.Prime) :
    ∃ t, searchLoop.Exec (checkedStore n) (checkedStore p) t ∧
      t ≤ (p-n) * stepBound p + 1 := by
  generalize hk : p-n = k
  induction k generalizing n with
  | zero =>
      have hEq : n = p := by omega
      subst n
      exact ⟨1, StackProg.Exec.loopFalse (test := guard)
        (by simp [guard, checkedStore, candidateStore_eq, hp]), by simp⟩
  | succ k ih =>
      obtain ⟨t, ht, htime⟩ := checkCurrent_exec (n+1) p (by omega) (by omega)
      obtain ⟨v, hv, hbudget⟩ := ih (n+1) (by omega) (by omega)
        (fun i hi hil => hfirst i (by omega) hil) (by omega)
      refine ⟨1+(1+1+t)+1+v, ?_, ?_⟩
      · exact StackProg.Exec.loopTrue (test := guard)
          (by simp [guard, checkedStore, candidateStore_eq, hfirst n le_rfl (by omega : n < p)])
          ((incrementCandidate_exec n [decide (¬n.Prime)]).seq ht) hv
      · rw [Nat.succ_mul]
        omega

private def raiseFloor : ℕ → StackProg (Fin 10) Bool
  | 0 => .act (fun _ _ => .keep)
  | k+1 => .seq (popProg 0) (.seq (raiseFloor k) incrementCandidate)

private theorem popCandidate_exec (n : ℕ) :
    (popProg (0 : Fin 10)).Exec (candidateStore n 0 0 [] [])
      (candidateStore (n-1) 0 0 [] []) 1 := by
  convert pop_exec (0 : Fin 10) (candidateStore n 0 0 [] []) using 1
  exact funext (fun k => by
    simp only [candidateStore_eq]
    fin_cases k <;> simp [List.tail_replicate])

private theorem raiseFloor_exec (B m : ℕ) :
    (raiseFloor B).Exec (candidateStore m 0 0 [] [])
      (candidateStore (max m B) 0 0 [] []) (4*B+1) := by
  induction B generalizing m with
  | zero =>
      rw [max_eq_left (Nat.zero_le m)]
      exact StackProg.Exec.act (fun _ _ => .keep) (candidateStore m 0 0 [] [])
  | succ B ih =>
      have hincr := incrementCandidate_exec (max (m-1) B) []
      have hmax : max (m-1) B + 1 = max m (B+1) := by omega
      have hr := (popCandidate_exec m).seq ((ih (m-1)).seq hincr)
      rw [hmax] at hr
      convert hr using 1 <;> first | rfl | omega

/-- Raise the input to the fixed lower bound, then search strictly above it. -/
noncomputable def leastPrime (B : ℕ) : StackProg (Fin 10) Bool :=
  .seq (raiseFloor B) (.seq incrementCandidate (.seq checkCurrent searchLoop))

theorem leastPrime_exec (B m p : ℕ) (hB : 0 < B) (hp : p.Prime) (hmp : max m B < p)
    (hfirst : ∀ i, max m B < i → i < p → ¬i.Prime) :
    ∃ t, (leastPrime B).Exec (candidateStore m 0 0 [] []) (checkedStore p) t ∧
      t ≤ 4*B + 6 + (p+1) * stepBound p := by
  let first := max m B + 1
  have hlow : 2 ≤ first := by dsimp [first]; omega
  have hhi : first ≤ p := by dsimp [first]; omega
  obtain ⟨u, hu, hub⟩ := checkCurrent_exec first p hlow hhi
  obtain ⟨v, hv, hvb⟩ := searchLoop_exec p first hlow hhi hp
    (fun i hi hip => hfirst i (by dsimp [first] at hi; omega) hip)
  refine ⟨_, (raiseFloor_exec B m).seq ((incrementCandidate_exec (max m B) []).seq (hu.seq hv)), ?_⟩
  have hsteps := Nat.mul_le_mul_right (stepBound p) (show p-first ≤ p by omega)
  simp only [Nat.succ_mul]
  omega

end FourToOneGames.WordMachines.PrimeScan

end

/- ChoosePrimeMachine -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.PrimeScan

open CookPvsNP

/-- Compute the reduction's prime in place on port zero, clearing all private tapes. -/
noncomputable def choosePrimeStack (B : ℕ) : StackProg (Fin 10) Bool :=
  .seq (leastPrime B) (popProg 9)

open Polynomial in
noncomputable def choosePrimeBudget (B : ℕ) : Polynomial ℕ :=
  let hi := 2*(X+C B)
  4*C B + 8 + (hi+1)*((12*(hi+1)*(hi+1)+9*hi+3*hi+22)*hi+20*hi+32)

private theorem budget_eval (B m : ℕ) :
    (choosePrimeBudget B).eval m =
      4*B + 8 + (2*(m+B)+1)*stepBound (2*(m+B)) := by
  simp [choosePrimeBudget, stepBound, trialBound]

private theorem stepBound_mono : Monotone stepBound := by
  intro a b h
  unfold stepBound trialBound
  gcongr

theorem choosePrimeBudget_mono (B : ℕ) : Monotone (choosePrimeBudget B).eval := by
  intro m n h
  simp only [budget_eval]
  exact Nat.add_le_add_left (Nat.mul_le_mul (by omega)
    (stepBound_mono (by omega))) _

theorem choosePrimeStack_exec (B m : ℕ) (hB : 0 < B) :
    ∃ t, (choosePrimeStack B).Exec (candidateStore m 0 0 [] [])
      (candidateStore (choosePrime B m hB) 0 0 [] []) t ∧
      t ≤ (choosePrimeBudget B).eval m := by
  let p := choosePrime B m hB
  obtain ⟨hp, hmp, hupper⟩ := choosePrime_spec B m hB
  have hfirst (i : ℕ) (hmi : max m B < i) (hip : i < p) : ¬i.Prime :=
    fun hi => (not_le_of_gt hip) (choosePrime_le_of_prime B m hB hi hmi)
  obtain ⟨t, ht, hb⟩ := leastPrime_exec B m p hB hp hmp hfirst
  have hpop : (popProg (9 : Fin 10)).Exec (checkedStore p) (candidateStore p 0 0 [] []) 1 := by
    convert pop_exec (9 : Fin 10) (checkedStore p) using 1
    exact funext (fun k => by
      simp only [checkedStore, candidateStore_eq]
      fin_cases k <;> rfl)
  refine ⟨_, ht.seq hpop, ?_⟩
  rw [budget_eval]
  have hhi : p ≤ 2*(m+B) := hupper.trans (by omega)
  have htime := Nat.mul_le_mul (Nat.add_le_add_right hhi 1) (stepBound_mono hhi)
  omega

def unaryCandidate (m : ℕ) : List Bool := List.replicate m true

/-- The least-prime function used by the lift has a TM2 certificate on unary inputs. -/
noncomputable def choosePrime_polytime (B : ℕ) (hB : 0 < B) :
    Turing.TM2ComputableInPolyTime unaryCandidate unaryCandidate (fun m => choosePrime B m hB) :=
  StackTM2Time.programPolytime unaryCandidate unaryCandidate (fun m => choosePrime B m hB)
    (choosePrimeStack B) 0 0 (choosePrimeBudget B) (fun m => by
      obtain ⟨t, he, hb⟩ := choosePrimeStack_exec B m hB
      have hinit : ((choosePrimeStack B).machine.init 0 (unaryCandidate m)).store =
          candidateStore m 0 0 [] [] := by
        funext k
        rw [candidateStore_eq]
        fin_cases k <;> rfl
      rw [← hinit] at he
      refine ⟨_, t, he, rfl, ?_⟩
      simpa only [unaryCandidate, List.length_replicate] using hb)

end FourToOneGames.WordMachines.PrimeScan

end

/- LiftInputMachine -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.LiftInput

open CookPvsNP OAI.PerfectCompleteness PrimeScan

theorem appendLeft_exec {n m : ℕ} {A : Type} {p : StackProg (Fin n) A} {s t : Fin n → List A}
    {u : ℕ} (h : p.Exec s t u) (frame : Fin m → List A) :
    (onPorts (Fin.castAddEmb m) p).Exec (Fin.append s frame) (Fin.append t frame) u := by
  refine onPorts_exec _ h (Fin.append_left _ _) (Fin.append_left _ _) ?_
  intro i hi
  refine Fin.addCases (fun l hl => (hl l rfl).elim) (fun r _ => ?_) i hi
  simp only [Fin.append_right]

theorem appendRight_exec {n m : ℕ} {A : Type} {p : StackProg (Fin m) A} {s t : Fin m → List A}
    {u : ℕ} (h : p.Exec s t u) (frame : Fin n → List A) :
    (onPorts (Fin.natAddEmb n) p).Exec (Fin.append frame s) (Fin.append frame t) u := by
  refine onPorts_exec _ h (Fin.append_right _ _) (Fin.append_right _ _) ?_
  intro i hi
  refine Fin.addCases (fun l _ => ?_) (fun r hr => (hr r rfl).elim) i hi
  simp only [Fin.append_left]

def recordBits {q : ℕ} (G : Instance q) : List Bool :=
  (G.edges.flatMap Encoding.edgeWords).flatMap (unary true false)

def headerStore {q : ℕ} (G : Instance q) : Fin 5 → List Bool :=
  ![recordBits G, List.replicate G.leftVertices true, List.replicate G.rightVertices true,
    List.replicate q true, List.replicate G.edges.length true]

/-- Preserve the original header and record table alongside the selected prime. -/
def loadedStore {q : ℕ} (G : Instance q) (p : ℕ) : Fin 15 → List Bool :=
  Fin.append (headerStore G) (candidateStore p 0 0 [] [])

noncomputable def load (B : ℕ) : StackProg (Fin 15) Bool :=
  .seq (onPorts (Fin.castAddEmb 10) (readFour true))
    (.seq (copyProg 4 5 6) (onPorts (Fin.natAddEmb 5) (choosePrimeStack B)))

open Polynomial in
noncomputable def loadBudget (B : ℕ) : Polynomial ℕ :=
  choosePrimeBudget B + 9*X + 20

theorem headerLength_le {q : ℕ} (G : Instance q) :
    G.leftVertices + G.rightVertices + q + G.edges.length + 4 ≤ (Encoding.gameBits G).length := by
  rw [gameBits_input_layout]
  simp [unary]
  omega

theorem recordBits_length_le {q : ℕ} (G : Instance q) :
    (recordBits G).length ≤ (Encoding.gameBits G).length := by
  rw [gameBits_input_layout]
  simp [recordBits]
  omega

/-- Bound all dense traversal counters in terms of the actual input length. -/
theorem liftSizeBounds {q : ℕ} (G : Instance q) (B : ℕ) (hB : 0 < B) :
    let len := (Encoding.gameBits G).length
    let p := choosePrime B G.edges.length hB
    let cap := 2*(len+B)
    p ≤ cap ∧ G.leftVertices*p^3 ≤ len*cap^3 ∧
      G.rightVertices*p^4 ≤ len*cap^4 ∧ 4*q ≤ 4*len := by
  dsimp only
  have hlen := headerLength_le G
  have hp := (choosePrime_spec B G.edges.length hB).2.2
  have hcap : choosePrime B G.edges.length hB ≤ 2*((Encoding.gameBits G).length+B) :=
    hp.trans (by omega)
  refine ⟨hcap, Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hcap 3),
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hcap 4), by omega⟩

private theorem candidate_apply (p : ℕ) (i : Fin 10) :
    candidateStore p 0 0 [] [] i = if i = 0 then List.replicate p true else [] := by
  rw [candidateStore_eq]
  fin_cases i <;> rfl

private theorem copyEdgeCount_exec {q : ℕ} (G : Instance q) :
    (copyProg (4 : Fin 15) 5 6).Exec (loadedStore G 0) (loadedStore G G.edges.length)
      (6*G.edges.length+3) := by
  let s := loadedStore G 0
  have hlen : (s 4).length = G.edges.length := by
    change (List.replicate G.edges.length true).length = G.edges.length
    simp
  have hdata : s 4 ++ s 5 = List.replicate G.edges.length true := by
    change List.replicate G.edges.length true ++ [] = _
    simp
  have hupdate : Function.update s 5 (s 4 ++ s 5) = loadedStore G G.edges.length := by
    funext k
    refine Fin.addCases (m := 5) (n := 10) (fun i => ?_) (fun j => ?_) k
    · have hne : i.castAdd 10 ≠ (5 : Fin 15) := by
        intro he
        have hi : i.val = 5 := congrArg Fin.val he
        omega
      simp only [Function.update_of_ne hne, s, loadedStore, Fin.append_left]
    · by_cases hj : j = 0
      · subst j
        change Function.update s 5 (s 4 ++ s 5) 5 = List.replicate G.edges.length true
        rw [Function.update_self, hdata]
      · have hne : j.natAdd 5 ≠ (5 : Fin 15) := by
          intro he
          have hh : 5 + j.val = 5 := congrArg Fin.val he
          exact hj (Fin.eq_of_val_eq (by omega))
        simp only [Function.update_of_ne hne, s, loadedStore, Fin.append_right, candidate_apply, if_neg hj]
  simpa only [hupdate, hlen] using
    stack_copy (4 : Fin 15) 5 6 (by decide) (by decide) (by decide) s (by rfl)

theorem load_exec {q : ℕ} (G : Instance q) (B : ℕ) (hB : 0 < B) :
    ∃ t, (load B).Exec (((load B).machine.init 0 (Encoding.gameBits G)).store)
      (loadedStore G (choosePrime B G.edges.length hB)) t ∧
      t ≤ (loadBudget B).eval (Encoding.gameBits G).length := by
  let empty := candidateStore 0 0 0 [] []
  let src : Fin 15 → List Bool := Fin.append ![Encoding.gameBits G, [], [], [], []] empty
  have hsrc : (((load B).machine.init 0 (Encoding.gameBits G)).store) = src := by
    funext k
    fin_cases k <;> rfl
  have hread : (onPorts (Fin.castAddEmb 10) (readFour true)).Exec src
      (loadedStore G 0) (3*(G.leftVertices + G.rightVertices + q + G.edges.length)+15) :=
    appendLeft_exec (twoToOne_header_exec G) empty
  obtain ⟨u, hprime, hbudget⟩ := choosePrimeStack_exec B G.edges.length hB
  have hrun := hread.seq ((copyEdgeCount_exec G).seq (appendRight_exec hprime (headerStore G)))
  refine ⟨_, hsrc.symm ▸ hrun, ?_⟩
  have hsum := headerLength_le G
  have hmono : (choosePrimeBudget B).eval G.edges.length ≤
      (choosePrimeBudget B).eval (Encoding.gameBits G).length :=
    choosePrimeBudget_mono B (show G.edges.length ≤ (Encoding.gameBits G).length by omega)
  simp only [loadBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

/-- Compute the prime directly from the published 2-to-1 encoding. -/
noncomputable def primeFromGame (q B : ℕ) (hB : 0 < B) :
    Turing.TM2ComputableInPolyTime (Encoding.gameBits (q := q)) unaryCandidate
      (fun G => choosePrime B G.edges.length hB) :=
  StackTM2Time.programPolytime Encoding.gameBits unaryCandidate
    (fun G => choosePrime B G.edges.length hB) (load B) 0 5 (loadBudget B) (fun G => by
      obtain ⟨t, he, hb⟩ := load_exec G B hB
      exact ⟨_, t, he, rfl, hb⟩)

end FourToOneGames.WordMachines.LiftInput

end

/- RecordLookupMachine -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.RecordLookup

open CookPvsNP OAI.PerfectCompleteness

private def store (w : List Bool) (record width field offset : ℕ)
    (out : List Bool) : Fin 9 → List Bool :=
  ![w, List.replicate record true, List.replicate width true, List.replicate field true,
    out, List.replicate offset true, [], [], []]

def inputStore (w : List Bool) (record width field : ℕ) (out : List Bool) : Fin 9 → List Bool :=
  store w record width field 0 out

private def mulPorts : Fin 5 ↪ Fin 9 := ⟨![1,2,5,6,7], by decide⟩
private def fieldPorts : Fin 6 ↪ Fin 9 := ⟨![0,5,4,6,7,8], by decide⟩

/-- Compute the flat field offset, read its unary value, and clear the offset tape. -/
noncomputable def readRecordField : StackProg (Fin 9) Bool :=
  .seq (onPorts mulPorts multiply)
    (.seq (copyProg 3 5 6) (.seq (onPorts fieldPorts (lookupField true)) (clearProg 5)))

def stepBound (wordLength record width field : ℕ) : ℕ :=
  (6*record+13)*width + 6*field + 10*wordLength + 13*(record*width+field) + 27

theorem readRecordField_exec (fields : List ℕ) (record width j : ℕ) (out : List Bool)
    (hj : record*width+j < fields.length) :
    let w := fields.flatMap (unary true false)
    ∃ t, readRecordField.Exec (inputStore w record width j out)
      (inputStore w record width j (List.replicate fields[record*width+j] true ++ out)) t ∧
      t ≤ stepBound w.length record width j := by
  let off := record*width+j
  let w := fields.flatMap (unary true false)
  let result := List.replicate fields[record*width+j] true ++ out
  let s0 := inputStore w record width j out
  let s1 := store w record width j (record*width) out
  let s2 := store w record width j off out
  let s3 := store w record width j off result
  let s4 := inputStore w record width j result
  have hmul : (onPorts mulPorts multiply).Exec s0 s1 ((6*record+13)*width+5) := by
    convert multiplyOn_exec mulPorts s0 true record width rfl rfl rfl rfl using 1
    exact funext (fun k => by fin_cases k <;> simp [s0, s1, inputStore, store, mulPorts])
  have hadd : (copyProg (3 : Fin 9) 5 6).Exec s1 s2 (6*j+3) := by
    convert stack_copy (3 : Fin 9) 5 6 (by decide) (by decide) (by decide) s1 rfl using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> simp [s1, s2, store, off, Nat.add_comm]) |
        solve | simp [s1, store]
  obtain ⟨u, hu, hub⟩ := lookupField_at true false fields (List.replicate off true) out
    (by decide) (by simpa only [List.length_replicate, off] using hj)
  have hget : (lookupField true).Exec (lookupStore w (List.replicate off true) out)
      (lookupStore w (List.replicate off true) result) u := by
    simpa only [result, List.length_replicate, off] using hu
  have hread : (onPorts fieldPorts (lookupField true)).Exec s2 s3 u := by
    refine onPorts_exec fieldPorts hget ?_ ?_ ?_
    · intro k
      fin_cases k <;> rfl
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      fin_cases k
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (hk 2 rfl).elim
      · rfl
      · rfl
      · rfl
      · rfl
  have hc : (clearProg (5 : Fin 9)).Exec s3 s4 (3*off+1) := by
    convert clear_exec (5 : Fin 9) s3 using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl) |
        solve | simp [s3, store]
  refine ⟨_, hmul.seq (hadd.seq (hread.seq hc)), ?_⟩
  simp only [List.length_replicate] at hub
  dsimp [stepBound]
  change u ≤ 10*w.length+10*off+15 at hub
  change _ ≤ (6*record+13)*width + 6*j + 10*w.length + 13*off + 27
  omega

private theorem recordField_lt {q : ℕ} (G : Instance q) (e : Fin G.edges.length)
    (j : ℕ) (hj : j < 2+2*q) :
    e.val*(2+2*q)+j < (G.edges.flatMap Encoding.edgeWords).length := by
  rw [twoToOne_payload_length]
  have hrow := Nat.mul_le_mul_right (2+2*q) (Nat.succ_le_of_lt e.isLt)
  rw [Nat.succ_mul] at hrow
  omega

/-- Read either endpoint of a record in the original 2-to-1 encoding. -/
theorem endpoint_exec {q : ℕ} (G : Instance q) (e : Fin G.edges.length)
    (right : Bool) (out : List Bool) :
    let w := LiftInput.recordBits G
    let v := if right then (G.edges.get e).right.val else (G.edges.get e).left.val
    ∃ t, readRecordField.Exec (inputStore w e.val (2+2*q) right.toNat out)
      (inputStore w e.val (2+2*q) right.toNat (List.replicate v true ++ out)) t ∧
      t ≤ stepBound w.length e.val (2+2*q) right.toNat := by
  have hj : right.toNat < 2+2*q := by
    cases right <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  simpa only [LiftInput.recordBits, twoToOne_endpoint_get] using
    readRecordField_exec (G.edges.flatMap Encoding.edgeWords) e.val (2+2*q)
      right.toNat out (recordField_lt G e right.toNat hj)

/-- Read an original projection image by edge ordinal and label. -/
theorem projection_exec {q : ℕ} (G : Instance q) (e : Fin G.edges.length)
    (a : Fin (2*q)) (out : List Bool) :
    let w := LiftInput.recordBits G
    let v := ((G.edges.get e).projection.images[a]).val
    ∃ t, readRecordField.Exec (inputStore w e.val (2+2*q) (2+a.val) out)
      (inputStore w e.val (2+2*q) (2+a.val) (List.replicate v true ++ out)) t ∧
      t ≤ stepBound w.length e.val (2+2*q) (2+a.val) := by
  simpa only [LiftInput.recordBits, twoToOne_projection_get] using
    readRecordField_exec (G.edges.flatMap Encoding.edgeWords) e.val (2+2*q)
      (2+a.val) out (recordField_lt G e (2+a.val) (by have := a.isLt; omega))

end FourToOneGames.WordMachines.RecordLookup

end

/- UnaryCompare -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.UnaryComparison

open CookPvsNP

private def state (a b l r : ℕ) (tail : List Bool) : Fin 6 → List Bool :=
  ![List.replicate a true, List.replicate b true, List.replicate l true,
    List.replicate r true, [], tail]

def inputStore (a b : ℕ) (tail : List Bool) : Fin 6 → List Bool := state a b 0 0 tail

private def both (h : Fin 6 → Option Bool) : Bool := (h 2).isSome && (h 3).isSome

private def consume : StackProg (Fin 6) Bool :=
  .act (fun _ k => if k = 2 ∨ k = 3 then .pop else .keep)

private def cancel : StackProg (Fin 6) Bool := .loop both consume

private def emit (less : Bool) : StackProg (Fin 6) Bool :=
  .act (fun h k => if k = 5 then
    .push (if less then (h 3).isSome else (h 2).isNone && (h 3).isNone)
  else .keep)

def compareProp (less : Bool) (a b : ℕ) : Prop := if less then a < b else a = b
instance (less : Bool) (a b : ℕ) : Decidable (compareProp less a b) := by
  unfold compareProp
  infer_instance

/-- Compare two unary registers, preserve both, and prepend the comparison bit. -/
def compare (less : Bool) : StackProg (Fin 6) Bool :=
  .seq (copyProg 0 2 4) (.seq (copyProg 1 3 4) (.seq cancel
    (.seq (emit less) (.seq (clearProg 2) (clearProg 3)))))

private theorem consume_exec (a b l r : ℕ) (tail : List Bool) :
    consume.Exec (state a b (l+1) (r+1) tail) (state a b l r tail) 1 := by
  unfold consume
  convert StackProg.Exec.act _ (state a b (l+1) (r+1) tail) using 1
  exact funext (fun k => by fin_cases k <;> rfl)

private theorem cancel_exec (a b l r : ℕ) (out : List Bool) :
    cancel.Exec (state a b l r out) (state a b (l-r) (r-l) out) (3*min l r+1) := by
  induction l generalizing r with
  | zero =>
      simpa [cancel, Nat.min_eq_left (Nat.zero_le r)] using
        StackProg.Exec.loopFalse (test := both) (p := consume) (s := state a b 0 r out) rfl
  | succ l ih =>
      cases r with
      | zero =>
          simpa [cancel, Nat.min_eq_right (Nat.zero_le (l+1))] using
            StackProg.Exec.loopFalse (test := both) (p := consume) (s := state a b (l+1) 0 out)
              (by rfl)
      | succ r =>
          have hr := StackProg.Exec.loopTrue (test := both) rfl (consume_exec a b l r out) (ih r)
          convert hr using 1 <;> first | rfl | (simp [Nat.succ_min_succ] <;> omega)

private theorem someUnary (n : ℕ) :
    ((List.replicate n true).head?).isSome = decide (0 < n) := by
  cases n <;> rfl

private theorem noneUnary (n : ℕ) :
    ((List.replicate n true).head?).isNone = decide (n = 0) := by
  cases n <;> rfl

private theorem emit_exec (less : Bool) (a b : ℕ) (out : List Bool) :
    (emit less).Exec (state a b (a-b) (b-a) out)
      (state a b (a-b) (b-a) (decide (compareProp less a b) :: out)) 1 := by
  have hlt : ((List.replicate (b-a) true).head?).isSome = decide (a < b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [someUnary, decide_eq_true_eq]
    omega
  have heq : (((List.replicate (a-b) true).head?).isNone &&
      ((List.replicate (b-a) true).head?).isNone) = decide (a = b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [noneUnary, Bool.and_eq_true, decide_eq_true_eq]
    omega
  unfold emit
  convert StackProg.Exec.act _ (state a b (a-b) (b-a) out) using 1
  exact funext (fun k => by fin_cases k <;> cases less <;>
    simp [state, StackProg.applyAct, StackAct.apply, compareProp, hlt, heq])

theorem compare_exec (less : Bool) (a b : ℕ) (out : List Bool) :
    ∃ t, (compare less).Exec (inputStore a b out)
      (inputStore a b (decide (compareProp less a b) :: out)) t ∧
      t ≤ 12*(a+b)+15 := by
  let flagged := decide (compareProp less a b) :: out
  have ha : (copyProg (0 : Fin 6) 2 4).Exec (state a b 0 0 out)
      (state a b a 0 out) (6*a+3) := by
    convert stack_copy (0 : Fin 6) 2 4 (by decide) (by decide) (by decide)
      (state a b 0 0 out) rfl using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> simp [state]) | solve | simp [state]
  have hb : (copyProg (1 : Fin 6) 3 4).Exec (state a b a 0 out)
      (state a b a b out) (6*b+3) := by
    convert stack_copy (1 : Fin 6) 3 4 (by decide) (by decide) (by decide)
      (state a b a 0 out) rfl using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> simp [state]) | solve | simp [state]
  have hc : (clearProg (2 : Fin 6)).Exec (state a b (a-b) (b-a) flagged)
      (state a b 0 (b-a) flagged) (3*(a-b)+1) := by
    convert clear_exec (2 : Fin 6) (state a b (a-b) (b-a) flagged) using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl) | solve | simp [state]
  have hd : (clearProg (3 : Fin 6)).Exec (state a b 0 (b-a) flagged)
      (state a b 0 0 flagged) (3*(b-a)+1) := by
    convert clear_exec (3 : Fin 6) (state a b 0 (b-a) flagged) using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl) | solve | simp [state]
  refine ⟨_, ha.seq (hb.seq ((cancel_exec a b a b out).seq
    ((emit_exec less a b out).seq (hc.seq hd)))), ?_⟩
  have hmin := min_le_left a b
  omega

end FourToOneGames.WordMachines.UnaryComparison

end

/- GuardedRecordMachine -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.RecordLookup

open CookPvsNP LiftInput

private def countFrame (count : ℕ) (flag : List Bool) : Fin 5 → List Bool :=
  ![List.replicate count true, flag, [], [], []]

def guardedStore (w : List Bool) (record count width j : ℕ)
    (out flag : List Bool) : Fin 14 → List Bool :=
  Fin.append (inputStore w record width j out) (countFrame count flag)

private def guardPorts : Fin 6 ↪ Fin 14 := ⟨![1,9,11,12,13,10], by decide⟩
private def guard (h : Fin 14 → Option Bool) : Bool := h 10 == some true
private def noop : StackProg (Fin 14) Bool := .act (fun _ _ => .keep)
private noncomputable def readInFrame : StackProg (Fin 14) Bool := onPorts (Fin.castAddEmb 5) readRecordField
private noncomputable def branchRead : StackProg (Fin 14) Bool := .branch guard readInFrame noop
private noncomputable def dropFlag : StackProg (Fin 14) Bool := onPorts (Fin.natAddEmb 9) (popProg (1 : Fin 5))

/-- Read a field only when its record index is below the retained count. -/
noncomputable def guardedRead : StackProg (Fin 14) Bool :=
  .seq (onPorts guardPorts (UnaryComparison.compare true)) (.seq branchRead dropFlag)

def guardedValue (fields : List ℕ) (record count width j : ℕ) : ℕ :=
  if record < count then fields.getD (record*width+j) 0 else 0

def guardedBound (n record count width j : ℕ) : ℕ :=
  stepBound n record width j + 12*(record+count)+20

private theorem check_exec (w : List Bool) (record count width j : ℕ) (out : List Bool) :
    ∃ t, (onPorts guardPorts (UnaryComparison.compare true)).Exec
      (guardedStore w record count width j out [])
      (guardedStore w record count width j out [decide (record<count)]) t ∧ t ≤ 12*(record+count)+15 := by
  obtain ⟨t, ht, hb⟩ := UnaryComparison.compare_exec true record count []
  have hprop : decide (UnaryComparison.compareProp true record count) = decide (record<count) := by
    simp [UnaryComparison.compareProp]
  rw [hprop] at ht
  refine ⟨t, onPorts_exec guardPorts ht ?_ ?_ ?_, hb⟩
  · intro k
    fin_cases k <;> rfl
  · intro k
    fin_cases k <;> rfl
  · intro k hk
    refine Fin.addCases (m := 9) (n := 5) (fun i _ => ?_) (fun i hi => ?_) k hk
    · simp only [guardedStore, Fin.append_left]
    · simp only [guardedStore, Fin.append_right]
      fin_cases i
      · rfl
      · exact (hi 5 rfl).elim
      · rfl
      · rfl
      · rfl

private theorem dropFlag_exec (w : List Bool) (record count width j : ℕ) (out : List Bool) (b : Bool) :
    dropFlag.Exec (guardedStore w record count width j out [b])
      (guardedStore w record count width j out []) 1 := by
  have h : (popProg (1 : Fin 5)).Exec (countFrame count [b]) (countFrame count []) 1 := by
    convert pop_exec (1 : Fin 5) (countFrame count [b]) using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  exact appendRight_exec h (inputStore w record width j out)

theorem guardedRead_exec (fields : List ℕ) (record count width j : ℕ) (out : List Bool)
    (hvalid : record < count → record*width+j < fields.length) :
    let w := fields.flatMap (unary true false)
    ∃ t, guardedRead.Exec (guardedStore w record count width j out [])
      (guardedStore w record count width j
        (List.replicate (guardedValue fields record count width j) true ++ out) []) t ∧
      t ≤ guardedBound w.length record count width j := by
  dsimp only
  let w := fields.flatMap (unary true false)
  let out' := List.replicate (guardedValue fields record count width j) true ++ out
  obtain ⟨t, ht, htb⟩ := check_exec w record count width j out
  by_cases h : record < count
  · have hval : guardedValue fields record count width j = fields[record*width+j]'(hvalid h) := by
      simp only [guardedValue, if_pos h, List.getD_eq_getElem fields 0 (hvalid h)]
    obtain ⟨u, hu, hub⟩ := readRecordField_exec fields record width j out (hvalid h)
    rw [← hval] at hu
    let flag := [decide (record<count)]
    have htest : guard (fun k => (guardedStore w record count width j out flag k).head?) = true := by
      change ([decide (record<count)].head? == some true) = true
      simp [h]
    have hread : readInFrame.Exec (guardedStore w record count width j out flag)
        (guardedStore w record count width j out' flag) u :=
      appendLeft_exec hu (countFrame count flag)
    have hb : branchRead.Exec (guardedStore w record count width j out flag)
        (guardedStore w record count width j out' flag) (1+u) :=
      StackProg.Exec.branchTrue (test := guard) (q := noop) htest hread
    refine ⟨_, ht.seq (hb.seq (dropFlag_exec w record count width j out' _)), ?_⟩
    change u ≤ stepBound w.length record width j at hub
    change _ ≤ guardedBound w.length record count width j
    unfold guardedBound
    omega
  · have hout : out' = out := by simp [out', guardedValue, h]
    let flag := [decide (record<count)]
    have htest : guard (fun k => (guardedStore w record count width j out flag k).head?) = false := by
      change ([decide (record<count)].head? == some true) = false
      simp [h]
    have hskip : noop.Exec (guardedStore w record count width j out flag)
        (guardedStore w record count width j out flag) 1 :=
      StackProg.Exec.act (fun _ _ => .keep) _
    have hb : branchRead.Exec (guardedStore w record count width j out flag)
        (guardedStore w record count width j out flag) (1+1) :=
      StackProg.Exec.branchFalse (test := guard) (p := readInFrame) htest hskip
    have he := ht.seq (hb.seq (dropFlag_exec w record count width j out _))
    change ∃ n, guardedRead.Exec (guardedStore w record count width j out [])
      (guardedStore w record count width j out' []) n ∧ n ≤ guardedBound w.length record count width j
    rw [hout]
    refine ⟨_, he, ?_⟩
    unfold guardedBound
    omega

end FourToOneGames.WordMachines.RecordLookup

end

/- LiftDimensions -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.LiftInput

open CookPvsNP OAI.PerfectCompleteness

private def squarePorts : Fin 5 ↪ Fin 15 := ⟨![5,6,7,13,14], by decide⟩
private def cubePorts : Fin 5 ↪ Fin 15 := ⟨![7,5,8,13,14], by decide⟩
private def fourthPorts : Fin 5 ↪ Fin 15 := ⟨![8,5,9,13,14], by decide⟩
private def leftPorts : Fin 5 ↪ Fin 15 := ⟨![1,8,10,13,14], by decide⟩
private def rightPorts : Fin 5 ↪ Fin 15 := ⟨![2,9,11,13,14], by decide⟩

private def setUnary (s : Fin 15 → List Bool) (port : Fin 15) (n : ℕ) :
    Fin 15 → List Bool := Function.update s port (List.replicate n true)

private def alphabetCopies : ℕ → StackProg (Fin 15) Bool
  | 0 => .act (fun _ _ => .keep)
  | k+1 => .seq (copyProg 3 12 13) (alphabetCopies k)

/-- Preserve the input and compute the radix powers, expanded sizes, and left alphabet size. -/
noncomputable def dimensions : StackProg (Fin 15) Bool :=
  .seq (copyProg 5 6 13) (.seq (onPorts squarePorts multiply)
    (.seq (onPorts cubePorts multiply) (.seq (onPorts fourthPorts multiply)
      (.seq (onPorts leftPorts multiply) (.seq (onPorts rightPorts multiply) (alphabetCopies 4))))))

/-- Ports ten, eleven, and twelve hold the output dimensions. -/
def dimensionStore {q : ℕ} (G : Instance q) (p : ℕ) : Fin 15 → List Bool :=
  ![recordBits G, List.replicate G.leftVertices true, List.replicate G.rightVertices true,
    List.replicate q true, List.replicate G.edges.length true, List.replicate p true,
    List.replicate p true, List.replicate (p^2) true, List.replicate (p^3) true,
    List.replicate (p^4) true, List.replicate (G.leftVertices*p^3) true,
    List.replicate (G.rightVertices*p^4) true, List.replicate (4*q) true, [], []]

def dimensionWork (l r q p : ℕ) : ℕ :=
  6*p + (6*p+13)*p + (6*p^2+13)*p + (6*p^3+13)*p +
    (6*l+13)*p^3 + (6*r+13)*p^4 + 24*q + 51

private theorem loaded_eq {q : ℕ} (G : Instance q) (p : ℕ) :
    loadedStore G p =
      ![recordBits G, List.replicate G.leftVertices true, List.replicate G.rightVertices true,
        List.replicate q true, List.replicate G.edges.length true, List.replicate p true,
        [], [], [], [], [], [], [], [], []] := by
  funext k
  fin_cases k <;> rfl

private theorem multiplyFresh_exec (e : Fin 5 ↪ Fin 15) (s : Fin 15 → List Bool) (a b : ℕ)
    (ha : s (e 0) = List.replicate a true) (hb : s (e 1) = List.replicate b true)
    (h2 : s (e 2) = []) (h3 : s (e 3) = []) (h4 : s (e 4) = []) :
    (onPorts e multiply).Exec s (setUnary s (e 2) (a*b)) ((6*a+13)*b+5) := by
  simpa only [setUnary, h2, List.append_nil] using multiplyOn_exec e s true a b ha hb h3 h4

private theorem alphabetCopies_exec (k q a : ℕ) (s : Fin 15 → List Bool)
    (hq : s 3 = List.replicate q true) (ha : s 12 = List.replicate a true) (hw : s 13 = []) :
    (alphabetCopies k).Exec s (setUnary s 12 (a+k*q)) (k*(6*q+4)+1) := by
  induction k generalizing s a with
  | zero =>
      have hsame : setUnary s 12 a = s := by
        rw [setUnary, ← ha, Function.update_eq_self]
      simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, hsame]
      exact StackProg.Exec.act (fun _ _ => .keep) s
  | succ k ih =>
      let next := setUnary s 12 (q+a)
      have hcopy : (copyProg (3 : Fin 15) 12 13).Exec s next (6*q+3) := by
        simpa only [hq, ha, List.length_replicate, ← List.replicate_add, next, setUnary] using
          stack_copy (3 : Fin 15) 12 13 (by decide) (by decide) (by decide) s hw
      have hrest := ih (q+a) next (by simp [next,setUnary,hq])
        (by simp [next,setUnary]) (by simp [next,setUnary,hw])
      have hr := hcopy.seq hrest
      have hout : setUnary next 12 (q+a+k*q) = setUnary s 12 (a+(k+1)*q) := by
        have hnat : q+a+k*q = a+(k+1)*q := by rw [Nat.succ_mul]; omega
        simp only [next, setUnary, Function.update_idem, hnat]
      rw [hout] at hr
      convert hr using 1 <;> first | rfl | (simp only [Nat.succ_mul]; omega)

theorem dimensions_exec {q : ℕ} (G : Instance q) (p : ℕ) :
    dimensions.Exec (loadedStore G p) (dimensionStore G p)
      (dimensionWork G.leftVertices G.rightVertices q p) := by
  let s0 := loadedStore G p
  let s1 := setUnary s0 6 p
  let s2 := setUnary s1 7 (p^2)
  let s3 := setUnary s2 8 (p^3)
  let s4 := setUnary s3 9 (p^4)
  let s5 := setUnary s4 10 (G.leftVertices*p^3)
  let s6 := setUnary s5 11 (G.rightVertices*p^4)
  let s7 := setUnary s6 12 (4*q)
  have hs : (copyProg (5 : Fin 15) 6 13).Exec s0 s1 (6*p+3) := by
    simpa [s0, s1, setUnary, loaded_eq] using
      stack_copy (5 : Fin 15) 6 13 (by decide) (by decide) (by decide) s0 rfl
  have hsquare : (onPorts squarePorts multiply).Exec s1 s2 ((6*p+13)*p+5) := by
    have h := multiplyFresh_exec squarePorts s1 p p
      (by simp [s0,s1,setUnary,squarePorts,loaded_eq])
      (by simp [s1,setUnary,squarePorts])
      (by simp [s0,s1,setUnary,squarePorts,loaded_eq])
      (by simp [s0,s1,setUnary,squarePorts,loaded_eq])
      (by simp [s0,s1,setUnary,squarePorts,loaded_eq])
    simpa [s2, squarePorts, pow_two] using h
  have hcube : (onPorts cubePorts multiply).Exec s2 s3 ((6*p^2+13)*p+5) := by
    have h := multiplyFresh_exec cubePorts s2 (p^2) p
      (by simp [s2,setUnary,cubePorts])
      (by simp [s0,s1,s2,setUnary,cubePorts,loaded_eq])
      (by simp [s0,s1,s2,setUnary,cubePorts,loaded_eq])
      (by simp [s0,s1,s2,setUnary,cubePorts,loaded_eq])
      (by simp [s0,s1,s2,setUnary,cubePorts,loaded_eq])
    simpa [s3, cubePorts, pow_succ p 2] using h
  have hfourth : (onPorts fourthPorts multiply).Exec s3 s4 ((6*p^3+13)*p+5) := by
    have h := multiplyFresh_exec fourthPorts s3 (p^3) p
      (by simp [s3,setUnary,fourthPorts])
      (by simp [s0,s1,s2,s3,setUnary,fourthPorts,loaded_eq])
      (by simp [s0,s1,s2,s3,setUnary,fourthPorts,loaded_eq])
      (by simp [s0,s1,s2,s3,setUnary,fourthPorts,loaded_eq])
      (by simp [s0,s1,s2,s3,setUnary,fourthPorts,loaded_eq])
    simpa [s4, fourthPorts, pow_succ p 3] using h
  have hleft : (onPorts leftPorts multiply).Exec s4 s5 ((6*G.leftVertices+13)*p^3+5) := by
    have h := multiplyFresh_exec leftPorts s4 G.leftVertices (p^3)
      (by simp [s0,s1,s2,s3,s4,setUnary,leftPorts,loaded_eq])
      (by simp [s3,s4,setUnary,leftPorts])
      (by simp [s0,s1,s2,s3,s4,setUnary,leftPorts,loaded_eq])
      (by simp [s0,s1,s2,s3,s4,setUnary,leftPorts,loaded_eq])
      (by simp [s0,s1,s2,s3,s4,setUnary,leftPorts,loaded_eq])
    simpa [s5, leftPorts] using h
  have hright : (onPorts rightPorts multiply).Exec s5 s6 ((6*G.rightVertices+13)*p^4+5) := by
    have h := multiplyFresh_exec rightPorts s5 G.rightVertices (p^4)
      (by simp [s0,s1,s2,s3,s4,s5,setUnary,rightPorts,loaded_eq])
      (by simp [s4,s5,setUnary,rightPorts])
      (by simp [s0,s1,s2,s3,s4,s5,setUnary,rightPorts,loaded_eq])
      (by simp [s0,s1,s2,s3,s4,s5,setUnary,rightPorts,loaded_eq])
      (by simp [s0,s1,s2,s3,s4,s5,setUnary,rightPorts,loaded_eq])
    simpa [s6, rightPorts] using h
  have ha : (alphabetCopies 4).Exec s6 s7 (24*q+17) := by
    have h := alphabetCopies_exec 4 q 0 s6
      (by simp [s0,s1,s2,s3,s4,s5,s6,setUnary,loaded_eq])
      (by simp [s0,s1,s2,s3,s4,s5,s6,setUnary,loaded_eq])
      (by simp [s0,s1,s2,s3,s4,s5,s6,setUnary,loaded_eq])
    have htime : 4*(6*q+4)+1 = 24*q+17 := by omega
    simpa only [Nat.zero_add, htime, s7] using h
  have hfinal : s7 = dimensionStore G p := by
    funext k
    fin_cases k <;> rfl
  have hrun := hs.seq (hsquare.seq (hcube.seq (hfourth.seq (hleft.seq (hright.seq ha)))))
  rw [hfinal] at hrun
  convert hrun using 1 <;> first | rfl | (unfold dimensionWork; omega)

private theorem dimensionWork_mono {l r q p len cap : ℕ}
    (hl : l ≤ len) (hr : r ≤ len) (hq : q ≤ len) (hp : p ≤ cap) :
    dimensionWork l r q p ≤ dimensionWork len len len cap := by
  unfold dimensionWork
  gcongr

open Polynomial in
private noncomputable def dimensionBudget (B : ℕ) : Polynomial ℕ :=
  let p := 2*(X+C B)
  6*p + (6*p+13)*p + (6*p^2+13)*p + (6*p^3+13)*p +
    (6*X+13)*p^3 + (6*X+13)*p^4 + 24*X + 51

private theorem eval_dimensionBudget (B n : ℕ) :
    (dimensionBudget B).eval n = dimensionWork n n n (2*(n+B)) := by
  simp [dimensionBudget, dimensionWork]

noncomputable def prepare (B : ℕ) : StackProg (Fin 15) Bool :=
  .seq (load B) dimensions

noncomputable def prepareBudget (B : ℕ) : Polynomial ℕ :=
  loadBudget B + dimensionBudget B + 1

theorem prepare_exec {q : ℕ} (G : Instance q) (B : ℕ) (hB : 0 < B) :
    ∃ t, (prepare B).Exec (((prepare B).machine.init 0 (Encoding.gameBits G)).store)
      (dimensionStore G (choosePrime B G.edges.length hB)) t ∧
      t ≤ (prepareBudget B).eval (Encoding.gameBits G).length := by
  obtain ⟨t, ht, hb⟩ := load_exec G B hB
  refine ⟨_, ht.seq (dimensions_exec G _), ?_⟩
  have hs := headerLength_le G
  have hp := (liftSizeBounds G B hB).1
  have hw := dimensionWork_mono (by omega : G.leftVertices ≤ (Encoding.gameBits G).length)
    (by omega : G.rightVertices ≤ (Encoding.gameBits G).length)
    (by omega : q ≤ (Encoding.gameBits G).length) hp
  simp only [prepareBudget, Polynomial.eval_add, Polynomial.eval_one, eval_dimensionBudget]
  omega

end FourToOneGames.WordMachines.LiftInput

end

/- LiftHeaderMachine -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines

open CookPvsNP

theorem pushBit_exec {K : Type} [DecidableEq K] (k : K) (b : Bool) (s : K → List Bool) :
    (pushProg k b).Exec s (Function.update s k (b :: s k)) 1 := by
  unfold pushProg
  convert StackProg.Exec.act _ s using 1
  exact funext (fun j => by by_cases h : j = k <;>
    simp [StackProg.applyAct, StackAct.apply, h])

/-- Prepend one delimited unary field while preserving its source register. -/
def prependUnary {K : Type} [DecidableEq K] (src out scratch : K) : StackProg K Bool :=
  .seq (pushProg out false) (copyProg src out scratch)

theorem prependUnary_exec {K : Type} [DecidableEq K] (src out scratch : K)
    (hso : src ≠ out) (hsw : src ≠ scratch) (how : out ≠ scratch)
    (s : K → List Bool) (n : ℕ) (hn : s src = List.replicate n true) (hw : s scratch = []) :
    (prependUnary src out scratch).Exec s
      (Function.update s out (unary true false n ++ s out)) (6*n+5) := by
  let mid := Function.update s out (false :: s out)
  have hsrc : mid src = List.replicate n true := by simpa [mid, hso] using hn
  have hout : mid out = false :: s out := by simp [mid]
  have hwork : mid scratch = [] := by simpa [mid, Ne.symm how] using hw
  have hcopy := stack_copy src out scratch hso hsw how mid hwork
  rw [hsrc, hout, List.length_replicate] at hcopy
  have hfinal : Function.update mid out (List.replicate n true ++ false :: s out) =
      Function.update s out (unary true false n ++ s out) := by
    simp [mid, unary, List.append_assoc]
  rw [hfinal] at hcopy
  have htime : 1+1+(6*n+3) = 6*n+5 := by omega
  simpa only [prependUnary, htime] using (pushBit_exec out false s).seq hcopy

namespace LiftInput

open OAI.PerfectCompleteness

def withOutput (s : Fin 15 → List Bool) (tail : List Bool) : Fin 16 → List Bool :=
  Fin.append s ![tail]

theorem withOutput_update (s : Fin 15 → List Bool) (tail next : List Bool) :
    Function.update (withOutput s tail) 15 next = withOutput s next := by
  funext k
  refine Fin.addCases (m := 15) (n := 1) (fun i => ?_) (fun j => ?_) k
  · have hi : i.castAdd 1 ≠ (15 : Fin 16) := by
      intro he
      have hv : i.val = 15 := congrArg Fin.val he
      omega
    simp only [Function.update_of_ne hi, withOutput, Fin.append_left]
  · fin_cases j
    rfl

def outputHeader {q : ℕ} (G : Instance q) (p : ℕ) : List Bool :=
  [G.leftVertices*p^3, G.rightVertices*p^4, 4*q, q].flatMap (unary true false)

/-- Prepend the exact lifted header to the already-produced adjacency and projection parts. -/
def writeHeader : StackProg (Fin 16) Bool :=
  .seq (prependUnary 3 15 13) (.seq (prependUnary 12 15 13)
    (.seq (prependUnary 11 15 13) (prependUnary 10 15 13)))

private theorem writeField_exec {q : ℕ} (G : Instance q) (p : ℕ) (src : Fin 15)
    (hsrc : src ≠ 13) (n : ℕ) (hn : dimensionStore G p src = List.replicate n true)
    (tail : List Bool) :
    (prependUnary (src.castAdd 1) 15 13).Exec (withOutput (dimensionStore G p) tail)
      (withOutput (dimensionStore G p) (unary true false n ++ tail)) (6*n+5) := by
  have hne : src.castAdd 1 ≠ (15 : Fin 16) := by
    intro he
    have hv : src.val = 15 := congrArg Fin.val he
    omega
  have hwork : src.castAdd 1 ≠ (13 : Fin 16) := fun he =>
    hsrc (Fin.ext (show src.val = 13 from congrArg (fun k : Fin 16 => k.val) he))
  have hreg : withOutput (dimensionStore G p) tail (src.castAdd 1) = List.replicate n true := by
    simpa only [withOutput, Fin.append_left] using hn
  have he := prependUnary_exec (src.castAdd 1) 15 13 hne hwork (by decide)
    (withOutput (dimensionStore G p) tail) n hreg (by rfl)
  rw [show withOutput (dimensionStore G p) tail 15 = tail from rfl, withOutput_update] at he
  exact he

theorem writeHeader_exec {q : ℕ} (G : Instance q) (p : ℕ) (tail : List Bool) :
    writeHeader.Exec (withOutput (dimensionStore G p) tail)
      (withOutput (dimensionStore G p) (outputHeader G p ++ tail))
      (6*(G.leftVertices*p^3+G.rightVertices*p^4+5*q)+23) := by
  let qTail := unary true false q ++ tail
  let lTail := unary true false (4*q) ++ qTail
  let rTail := unary true false (G.rightVertices*p^4) ++ lTail
  have hq := writeField_exec G p 3 (by decide) q rfl tail
  have hl := writeField_exec G p 12 (by decide) (4*q) rfl qTail
  have hr := writeField_exec G p 11 (by decide) (G.rightVertices*p^4) rfl lTail
  have hv := writeField_exec G p 10 (by decide) (G.leftVertices*p^3) rfl rTail
  have hrun := hq.seq (hl.seq (hr.seq hv))
  have hout : unary true false (G.leftVertices*p^3) ++ rTail = outputHeader G p ++ tail := by
    simp [outputHeader, rTail, lTail, qTail, List.append_assoc]
  rw [hout] at hrun
  convert hrun using 1 <;> first | rfl | omega

open Polynomial in
noncomputable def headerBudget (B : ℕ) : Polynomial ℕ :=
  let cap := 2*(X+C B)
  6*(X*cap^3+X*cap^4+5*X)+23

theorem headerBudget_ge {q : ℕ} (G : Instance q) (B : ℕ) (hB : 0 < B) :
    let p := choosePrime B G.edges.length hB
    6*(G.leftVertices*p^3+G.rightVertices*p^4+5*q)+23 ≤
      (headerBudget B).eval (Encoding.gameBits G).length := by
  dsimp only
  obtain ⟨_, hl, hr, _⟩ := liftSizeBounds G B hB
  have hq := headerLength_le G
  simp [headerBudget]
  omega

noncomputable def prepareOutput (B : ℕ) : StackProg (Fin 16) Bool :=
  onPorts (Fin.castAddEmb 1) (prepare B)

theorem prepareOutput_exec {q : ℕ} (G : Instance q) (B : ℕ) (hB : 0 < B) :
    ∃ t, (prepareOutput B).Exec
      (((prepareOutput B).machine.init 0 (Encoding.gameBits G)).store)
      (withOutput (dimensionStore G (choosePrime B G.edges.length hB)) []) t ∧
      t ≤ (prepareBudget B).eval (Encoding.gameBits G).length := by
  obtain ⟨t, ht, hb⟩ := prepare_exec G B hB
  have he := appendLeft_exec ht (![[]] : Fin 1 → List Bool)
  have hs : (((prepareOutput B).machine.init 0 (Encoding.gameBits G)).store) =
      withOutput (((prepare B).machine.init 0 (Encoding.gameBits G)).store) [] := by
    funext k
    fin_cases k <;> rfl
  exact ⟨t, hs.symm ▸ he, hb⟩

/-- The polynomial-time header transducer on the exact source encoding. -/
noncomputable def headerFromGame (q B : ℕ) (hB : 0 < B) :
    Turing.TM2ComputableInPolyTime (Encoding.gameBits (q := q)) id
      (fun G => outputHeader G (choosePrime B G.edges.length hB)) :=
  StackTM2Time.programPolytime Encoding.gameBits id
    (fun G => outputHeader G (choosePrime B G.edges.length hB))
    (.seq (prepareOutput B) writeHeader) 0 15 (prepareBudget B + headerBudget B + 1) (fun G => by
      let p := choosePrime B G.edges.length hB
      obtain ⟨t, ht, hb⟩ := prepareOutput_exec G B hB
      have hw := writeHeader_exec G p []
      refine ⟨_, _, ht.seq hw, ?_, ?_⟩
      · change outputHeader G p ++ [] = outputHeader G p
        simp
      · have hh := headerBudget_ge G B hB
        dsimp only at hh
        change 6*(G.leftVertices*p^3+G.rightVertices*p^4+5*q)+23 ≤ _ at hh
        simp only [Polynomial.eval_add, Polynomial.eval_one]
        omega)

end LiftInput
end FourToOneGames.WordMachines

end

/- LiftAdjacencyCell -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines

open CookPvsNP

theorem compareOn_exec {K : Type} [DecidableEq K] (ports : Fin 6 ↪ K)
    (s : K → List Bool) (less : Bool) (a b : ℕ)
    (ha : s (ports 0) = List.replicate a true) (hb : s (ports 1) = List.replicate b true)
    (h2 : s (ports 2) = []) (h3 : s (ports 3) = []) (h4 : s (ports 4) = []) :
    ∃ t, (onPorts ports (UnaryComparison.compare less)).Exec s
      (Function.update s (ports 5) (decide (UnaryComparison.compareProp less a b) :: s (ports 5))) t ∧
      t ≤ 12*(a+b)+15 := by
  obtain ⟨t, ht, hbnd⟩ := UnaryComparison.compare_exec less a b (s (ports 5))
  change (UnaryComparison.compare less).Exec
    ![List.replicate a true, List.replicate b true, [], [], [], s (ports 5)]
    ![List.replicate a true, List.replicate b true, [], [], [],
      decide (UnaryComparison.compareProp less a b) :: s (ports 5)] t at ht
  refine ⟨t, onPorts_exec ports ht ?_ ?_ ?_, hbnd⟩
  · intro i
    fin_cases i <;> simp [ha, hb, h2, h3, h4]
  · intro i
    fin_cases i <;> simp [ha, hb, h2, h3, h4, ports.injective.eq_iff]
  · intro i hi
    simp only [Function.update_of_ne (Ne.symm (hi 5))]

namespace LiftOutput

open RecordLookup LiftInput OAI.PerfectCompleteness

def adjacencyStore (w : List Bool) (record count width x y slot image : ℕ)
    (out left right valid : List Bool) : Fin 20 → List Bool :=
  Fin.append (guardedStore w record count width slot (List.replicate image true) [])
    ![List.replicate x true, List.replicate y true, out, left, right, valid]

private def leftCompare : Fin 6 ↪ Fin 20 := ⟨![4,14,11,12,13,17], by decide⟩
private def rightCompare : Fin 6 ↪ Fin 20 := ⟨![4,15,11,12,13,18], by decide⟩
private def countCompare : Fin 6 ↪ Fin 20 := ⟨![1,9,11,12,13,19], by decide⟩

private def emitEdge : StackProg (Fin 20) Bool :=
  .act (fun h k =>
    if k = 16 then .push (h 17 == some true && h 18 == some true && h 19 == some true)
    else if k = 17 ∨ k = 18 ∨ k = 19 then .pop else .keep)

private noncomputable def readEndpoint : StackProg (Fin 20) Bool :=
  onPorts (Fin.castAddEmb 6) guardedRead

/-- Compare both stored endpoints and require the ordinal to name an actual record. -/
noncomputable def emitAdjacencyBit : StackProg (Fin 20) Bool :=
  .seq readEndpoint (.seq (onPorts leftCompare (UnaryComparison.compare false))
    (.seq (clearProg 4) (.seq (pushProg 3 true) (.seq readEndpoint
      (.seq (onPorts rightCompare (UnaryComparison.compare false))
        (.seq (clearProg 4) (.seq (popProg 3)
          (.seq (onPorts countCompare (UnaryComparison.compare true)) emitEdge))))))))

def adjacencyValueBound (n record count width x y cap : ℕ) : ℕ :=
  guardedBound n record count width 0 + guardedBound n record count width 1 +
    12*(cap+x) + 12*(cap+y) + 12*(record+count) + 6*cap + 80

private theorem clearImage_exec (w : List Bool) (record count width x y slot image : ℕ)
    (out left right valid : List Bool) :
    (clearProg (4 : Fin 20)).Exec (adjacencyStore w record count width x y slot image out left right valid)
      (adjacencyStore w record count width x y slot 0 out left right valid) (3*image+1) := by
  convert clear_exec (4 : Fin 20) (adjacencyStore w record count width x y slot image out left right valid)
    using 1 <;> first | rfl | exact funext (fun k => by fin_cases k <;> rfl) |
      solve | change 3*image+1 = 3*(List.replicate image true).length+1; simp

private theorem emitEdge_exec (w : List Bool) (record count width x y : ℕ)
    (out : List Bool) (left right valid : Bool) :
    emitEdge.Exec (adjacencyStore w record count width x y 0 0 out [left] [right] [valid])
      (adjacencyStore w record count width x y 0 0 ((left && right && valid) :: out) [] [] []) 1 := by
  unfold emitEdge
  convert StackProg.Exec.act _ (adjacencyStore w record count width x y 0 0 out [left] [right] [valid])
    using 1
  exact funext (fun k => by fin_cases k <;> first | rfl | (cases left <;> cases right <;> cases valid <;> rfl))

theorem emitAdjacencyBit_exec (fields : List ℕ) (record count width x y cap : ℕ)
    (out : List Bool) (hvalid : ∀ j < 2, record < count → record*width+j < fields.length)
    (hcap : ∀ j < 2, guardedValue fields record count width j ≤ cap) :
    let w := fields.flatMap (unary true false)
    let bit := decide (guardedValue fields record count width 0 = x ∧
      guardedValue fields record count width 1 = y ∧ record < count)
    ∃ t, emitAdjacencyBit.Exec (adjacencyStore w record count width x y 0 0 out [] [] [])
      (adjacencyStore w record count width x y 0 0 (bit :: out) [] [] []) t ∧
      t ≤ adjacencyValueBound w.length record count width x y cap := by
  dsimp only
  let w := fields.flatMap (unary true false)
  let l := guardedValue fields record count width 0
  let r := guardedValue fields record count width 1
  let yesL := decide (l=x)
  let yesR := decide (r=y)
  let ok := decide (record<count)
  let s := adjacencyStore w record count width x y
  obtain ⟨tL, hL, hLb⟩ := guardedRead_exec fields record count width 0 []
    (hvalid 0 (by decide))
  rw [List.append_nil] at hL
  have hreadL : readEndpoint.Exec (s 0 0 out [] [] []) (s 0 l out [] [] []) tL :=
    appendLeft_exec hL (![List.replicate x true,List.replicate y true,out,[],[],[]] : Fin 6 → List Bool)
  obtain ⟨tCL, hCL, hCLb⟩ := compareOn_exec leftCompare (s 0 l out [] [] []) false l x
    rfl rfl rfl rfl rfl
  have hcmpL : (onPorts leftCompare (UnaryComparison.compare false)).Exec (s 0 l out [] [] [])
      (s 0 l out [yesL] [] []) tCL := by
    convert hCL using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have hclearL := clearImage_exec w record count width x y 0 l out [yesL] [] []
  have hset : (pushProg (3 : Fin 20) true).Exec (s 0 0 out [yesL] [] [])
      (s 1 0 out [yesL] [] []) 1 := by
    convert pushBit_exec (3 : Fin 20) true (s 0 0 out [yesL] [] []) using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  obtain ⟨tR, hR, hRb⟩ := guardedRead_exec fields record count width 1 []
    (hvalid 1 (by decide))
  rw [List.append_nil] at hR
  have hreadR : readEndpoint.Exec (s 1 0 out [yesL] [] []) (s 1 r out [yesL] [] []) tR :=
    appendLeft_exec hR (![List.replicate x true,List.replicate y true,out,[yesL],[],[]] :
      Fin 6 → List Bool)
  obtain ⟨tCR, hCR, hCRb⟩ := compareOn_exec rightCompare (s 1 r out [yesL] [] []) false r y
    rfl rfl rfl rfl rfl
  have hcmpR : (onPorts rightCompare (UnaryComparison.compare false)).Exec (s 1 r out [yesL] [] [])
      (s 1 r out [yesL] [yesR] []) tCR := by
    convert hCR using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have hclearR := clearImage_exec w record count width x y 1 r out [yesL] [yesR] []
  have hreset : (popProg (3 : Fin 20)).Exec (s 1 0 out [yesL] [yesR] [])
      (s 0 0 out [yesL] [yesR] []) 1 := by
    convert pop_exec (3 : Fin 20) (s 1 0 out [yesL] [yesR] []) using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  obtain ⟨tC, hC, hCb⟩ := compareOn_exec countCompare (s 0 0 out [yesL] [yesR] []) true record count
    rfl rfl rfl rfl rfl
  have hcmp : (onPorts countCompare (UnaryComparison.compare true)).Exec
      (s 0 0 out [yesL] [yesR] []) (s 0 0 out [yesL] [yesR] [ok]) tC := by
    convert hC using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have hemit := emitEdge_exec w record count width x y out yesL yesR ok
  have hb : (yesL && yesR && ok) = decide (l=x ∧ r=y ∧ record<count) := by
    apply Bool.eq_iff_iff.mpr
    simp [yesL, yesR, ok, and_assoc]
  rw [hb] at hemit
  refine ⟨_, hreadL.seq (hcmpL.seq (hclearL.seq (hset.seq (hreadR.seq
    (hcmpR.seq (hclearR.seq (hreset.seq (hcmp.seq hemit)))))))), ?_⟩
  have hl : l ≤ cap := hcap 0 (by decide)
  have hr : r ≤ cap := hcap 1 (by decide)
  change tL ≤ guardedBound w.length record count width 0 at hLb
  change tR ≤ guardedBound w.length record count width 1 at hRb
  change _ ≤ adjacencyValueBound w.length record count width x y cap
  unfold adjacencyValueBound
  omega

theorem emitAdjacencyAt_exec {q : ℕ} (G : Instance q) (p u v : ℕ) (out : List Bool) :
    let e := ordinal p u v
    let w := recordBits G
    let x := u/p^3
    let y := v/p^4
    ∃ t, emitAdjacencyBit.Exec (adjacencyStore w e G.edges.length (2+2*q) x y 0 0 out [] [] [])
      (adjacencyStore w e G.edges.length (2+2*q) x y 0 0 (edgeBit G p u v :: out) [] [] []) t ∧
      t ≤ adjacencyValueBound w.length e G.edges.length (2+2*q) x y
        (G.leftVertices+G.rightVertices) := by
  let fields := G.edges.flatMap Encoding.edgeWords
  let e := ordinal p u v
  let width := 2+2*q
  have hvalid (j : ℕ) (hj : j < 2) (he : e < G.edges.length) :
      e*width+j < fields.length := by
    change _ < (G.edges.flatMap Encoding.edgeWords).length
    rw [twoToOne_payload_length]
    have hrow := Nat.mul_le_mul_right width (Nat.succ_le_of_lt he)
    change (e+1)*width ≤ G.edges.length*width at hrow
    have hw : 2 ≤ width := by dsimp [width]; omega
    change _ < G.edges.length*width
    simp only [Nat.succ_mul] at hrow
    omega
  have endpoint (right : Bool) (he : e < G.edges.length) :
      guardedValue fields e G.edges.length width right.toNat =
        if right then (G.edges.get ⟨e,he⟩).right.val else (G.edges.get ⟨e,he⟩).left.val := by
    have hj : right.toNat < 2 := by cases right <;> decide
    rw [guardedValue, if_pos he, List.getD_eq_getElem fields 0 (hvalid _ hj he)]
    exact twoToOne_endpoint_get G ⟨e,he⟩ right
  have hcap (j : ℕ) (hj : j < 2) :
      guardedValue fields e G.edges.length width j ≤ G.leftVertices+G.rightVertices := by
    by_cases he : e < G.edges.length
    · rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
      · have hl : guardedValue fields e G.edges.length width 0 = (G.edges.get ⟨e,he⟩).left.val :=
          endpoint false he
        rw [hl]
        exact (G.edges.get ⟨e,he⟩).left.isLt.le.trans (Nat.le_add_right _ _)
      · have hr : guardedValue fields e G.edges.length width 1 = (G.edges.get ⟨e,he⟩).right.val :=
          endpoint true he
        rw [hr]
        exact (G.edges.get ⟨e,he⟩).right.isLt.le.trans (Nat.le_add_left _ _)
    · simp [guardedValue, he]
  have hbit : decide (guardedValue fields e G.edges.length width 0 = u/p^3 ∧
      guardedValue fields e G.edges.length width 1 = v/p^4 ∧ e < G.edges.length) = edgeBit G p u v := by
    by_cases he : e < G.edges.length
    · have hl : guardedValue fields e G.edges.length width 0 = (G.edges.get ⟨e,he⟩).left.val :=
        endpoint false he
      have hr : guardedValue fields e G.edges.length width 1 = (G.edges.get ⟨e,he⟩).right.val :=
        endpoint true he
      rw [hl, hr]
      change _ = (if h : e < G.edges.length then
        decide ((G.edges.get ⟨e,h⟩).left.val = u/p^3 ∧ (G.edges.get ⟨e,h⟩).right.val = v/p^4)
        else false)
      simp [he]
    · simp [edgeBit, ← show e = ordinal p u v from rfl, he]
  obtain ⟨t, ht, hb⟩ := emitAdjacencyBit_exec fields e G.edges.length width
    (u/p^3) (v/p^4) (G.leftVertices+G.rightVertices) out hvalid hcap
  rw [hbit] at ht
  exact ⟨t, ht, hb⟩

end LiftOutput
end FourToOneGames.WordMachines

end

/- UnaryPairMachine -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.UnaryPair

open CookPvsNP

private def state (a b work : ℕ) (out flag : List Bool) : Fin 8 → List Bool :=
  ![List.replicate a true, List.replicate b true, out, flag,
    [], [], [], List.replicate work true]

def inputStore (a b : ℕ) (out : List Bool) : Fin 8 → List Bool := state a b 0 out []

private def operand (right : Bool) : Fin 8 := if right then 1 else 0

private def squarePorts (right : Bool) : Fin 5 ↪ Fin 8 :=
  ⟨![operand right,7,2,4,5], by cases right <;> decide⟩

private def comparisonPorts : Fin 6 ↪ Fin 8 := ⟨![0,1,4,5,6,3], by decide⟩
private def test (h : Fin 8 → Option Bool) : Bool := h 3 == some true

private noncomputable def square (right : Bool) : StackProg (Fin 8) Bool :=
  .seq (copyProg (operand right) 7 4)
    (.seq (onPorts (squarePorts right) multiply) (clearProg 7))

private noncomputable def largerRight : StackProg (Fin 8) Bool :=
  .seq (square true) (copyProg 0 2 4)

private noncomputable def largerLeft : StackProg (Fin 8) Bool :=
  .seq (square false) (.seq (copyProg 0 2 4) (copyProg 1 2 4))

/-- Compute Nat.pair in unary, preserving both operands and prepending to an output tail. -/
noncomputable def pairMachine : StackProg (Fin 8) Bool :=
  .seq (onPorts comparisonPorts (UnaryComparison.compare true))
    (.seq (.branch test largerRight largerLeft) (popProg 3))

def pairBound (n : ℕ) : ℕ := (6*n+13)*n + 30*n + 50

private theorem square_exec (a b : ℕ) (out flag : List Bool) (right : Bool) :
    let n := if right then b else a
    (square right).Exec (state a b 0 out flag)
      (state a b 0 (List.replicate (n*n) true ++ out) flag) ((6*n+13)*n+9*n+11) := by
  dsimp only
  let n := if right then b else a
  have hsrc (work : ℕ) : state a b work out flag (operand right) = List.replicate n true := by
    cases right <;> rfl
  have hcopy : (copyProg (operand right) 7 4).Exec (state a b 0 out flag)
      (state a b n out flag) (6*n+3) := by
    have h := stack_copy (operand right) (7 : Fin 8) 4 (by cases right <;> decide)
      (by cases right <;> decide) (by decide) (state a b 0 out flag) rfl
    rw [hsrc, List.length_replicate] at h
    convert h using 1
    exact funext (fun k => by fin_cases k <;> simp [state])
  let next := List.replicate (n*n) true ++ out
  have hmul : (onPorts (squarePorts right) multiply).Exec (state a b n out flag)
      (state a b n next flag) ((6*n+13)*n+5) := by
    have h := multiplyOn_exec (squarePorts right) (state a b n out flag) true n n
      (hsrc n) rfl rfl rfl
    convert h using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have hc : (clearProg (7 : Fin 8)).Exec (state a b n next flag) (state a b 0 next flag) (3*n+1) := by
    convert clear_exec (7 : Fin 8) (state a b n next flag) using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl) | solve | simp [state]
  convert hcopy.seq (hmul.seq hc) using 1 <;>
    first | rfl | (change (6*n+13)*n+9*n+11 = _; omega)

private theorem prependOperand_exec (a b : ℕ) (out flag : List Bool) (right : Bool) :
    let n := if right then b else a
    (copyProg (operand right) 2 4).Exec (state a b 0 out flag)
      (state a b 0 (List.replicate n true ++ out) flag) (6*n+3) := by
  dsimp only
  let n := if right then b else a
  have hsrc : state a b 0 out flag (operand right) = List.replicate n true := by
    cases right <;> rfl
  have h := stack_copy (operand right) (2 : Fin 8) 4 (by cases right <;> decide)
    (by cases right <;> decide) (by decide) (state a b 0 out flag) rfl
  rw [hsrc, List.length_replicate] at h
  convert h using 1
  exact funext (fun k => by fin_cases k <;> rfl)

theorem pairMachine_exec (a b : ℕ) (out : List Bool) :
    ∃ t, pairMachine.Exec (inputStore a b out)
      (inputStore a b (List.replicate (Nat.pair a b) true ++ out)) t ∧
      t ≤ pairBound (a+b) := by
  let flag := [decide (a < b)]
  let s := a + b
  obtain ⟨t, hcmp, hct⟩ := compareOn_exec comparisonPorts (state a b 0 out [])
    true a b rfl rfl rfl rfl rfl
  have hcmp' : (onPorts comparisonPorts (UnaryComparison.compare true)).Exec
      (inputStore a b out) (state a b 0 out flag) t := by
    have hstate : state a b 0 out flag = Function.update (state a b 0 out [])
        (comparisonPorts 5) (decide (UnaryComparison.compareProp true a b) ::
          state a b 0 out [] (comparisonPorts 5)) := by
      exact funext (fun k => by fin_cases k <;> rfl)
    rw [hstate]
    exact hcmp
  let result := List.replicate (Nat.pair a b) true ++ out
  have hpop : (popProg (3 : Fin 8)).Exec (state a b 0 result flag) (inputStore a b result) 1 := by
    convert pop_exec (3 : Fin 8) (state a b 0 result flag) using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have hsq_le {n : ℕ} (hn : n ≤ s) : (6*n+13)*n ≤ (6*s+13)*s := by
    gcongr
  by_cases hab : a < b
  · let tail := List.replicate (b*b) true ++ out
    have hguard : test (fun k => (state a b 0 out flag k).head?) = true := by
      change (some (decide (a < b)) == some true) = true
      simp [hab]
    have hword : List.replicate a true ++ tail = result := by
      simp only [tail, result, Nat.pair, if_pos hab, ← List.append_assoc, ← List.replicate_add]
      rw [Nat.add_comm a]
    have hsq := square_exec a b out flag true
    have hcopy := prependOperand_exec a b tail flag false
    change (square true).Exec _ (state a b 0 tail flag) ((6*b+13)*b+9*b+11) at hsq
    change (copyProg 0 2 4).Exec _ (state a b 0 (List.replicate a true ++ tail) flag) (6*a+3) at hcopy
    rw [hword] at hcopy
    have hbranch := StackProg.Exec.branchTrue (q := largerLeft) hguard (hsq.seq hcopy)
    refine ⟨_, hcmp'.seq (hbranch.seq hpop), ?_⟩
    have hbound := hsq_le (n := b) (by dsimp [s]; omega)
    dsimp [pairBound, s] at hbound ⊢
    omega
  · let tail := List.replicate (a*a) true ++ out
    let tail' := List.replicate a true ++ tail
    have hguard : test (fun k => (state a b 0 out flag k).head?) = false := by
      change (some (decide (a < b)) == some true) = false
      simp [hab]
    have hword : List.replicate b true ++ tail' = result := by
      simp only [tail', tail, result, Nat.pair, if_neg hab, ← List.append_assoc, ← List.replicate_add]
      rw [show b+(a+a*a) = a*a+a+b by omega]
    have hsq := square_exec a b out flag false
    have hcopy := prependOperand_exec a b tail flag false
    have hcopy' := prependOperand_exec a b tail' flag true
    change (square false).Exec _ (state a b 0 tail flag) ((6*a+13)*a+9*a+11) at hsq
    change (copyProg 0 2 4).Exec _ (state a b 0 tail' flag) (6*a+3) at hcopy
    change (copyProg 1 2 4).Exec _ (state a b 0 (List.replicate b true ++ tail') flag) (6*b+3) at hcopy'
    rw [hword] at hcopy'
    have hbranch := StackProg.Exec.branchFalse (p := largerRight) hguard (hsq.seq (hcopy.seq hcopy'))
    refine ⟨_, hcmp'.seq (hbranch.seq hpop), ?_⟩
    have hbound := hsq_le (n := a) (by dsimp [s]; omega)
    dsimp [pairBound, s] at hbound ⊢
    omega

end FourToOneGames.WordMachines.UnaryPair

end

/- LiftProjectionCell -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.LiftOutput

open CookPvsNP LiftInput RecordLookup Radix OAI.PerfectCompleteness

def projectionStore (w : List Bool) (record count width label slot remainder : ℕ)
    (out : List Bool) : Fin 17 → List Bool :=
  Fin.append (guardedStore w record count width slot out [])
    ![List.replicate label true, [true,true], List.replicate remainder true]

private def halfPorts : Fin 6 ↪ Fin 17 := ⟨![3,15,11,12,16,13], by decide⟩

/-- Emit a unary projection field and restore the caller's input and scratch tapes. -/
noncomputable def emitProjectionValue : StackProg (Fin 17) Bool :=
  .seq (copyProg 14 3 11) (.seq (onPorts halfPorts extract)
    (.seq (pushProg 3 true) (.seq (pushProg 3 true) (.seq (pushProg 4 false)
      (.seq (onPorts (Fin.castAddEmb 3) guardedRead) (.seq (clearProg 3) (clearProg 16)))))))

def projectionValueBound (n record count width label : ℕ) : ℕ :=
  10*label + extractBound label 2 + guardedBound n record count width (2+label) + 30

private theorem store_eq (w : List Bool) (record count width label slot rem : ℕ) (out : List Bool) :
    projectionStore w record count width label slot rem out =
      ![w, List.replicate record true, List.replicate width true, List.replicate slot true,
        out, [], [], [], [], List.replicate count true, [], [], [], [],
        List.replicate label true, [true,true], List.replicate rem true] := by
  funext k
  fin_cases k <;> rfl

private theorem pushSlot_exec (w : List Bool) (record count width label slot rem : ℕ) (out : List Bool) :
    (pushProg (3 : Fin 17) true).Exec (projectionStore w record count width label slot rem out)
      (projectionStore w record count width label (slot+1) rem out) 1 := by
  convert pushBit_exec (3 : Fin 17) true (projectionStore w record count width label slot rem out) using 1
  exact funext (fun k => by rw [store_eq, store_eq]; fin_cases k <;> rfl)

private theorem writeSeparator_exec (w : List Bool) (record count width label slot rem : ℕ)
    (out : List Bool) :
    (pushProg (4 : Fin 17) false).Exec (projectionStore w record count width label slot rem out)
      (projectionStore w record count width label slot rem (false :: out)) 1 := by
  convert pushBit_exec (4 : Fin 17) false (projectionStore w record count width label slot rem out) using 1
  exact funext (fun k => by rw [store_eq, store_eq]; fin_cases k <;> rfl)

theorem emitProjectionValue_exec (fields : List ℕ) (record count width label : ℕ)
    (out : List Bool) (hvalid : record < count → record*width+(2+label/2) < fields.length) :
    let w := fields.flatMap (unary true false)
    ∃ t, emitProjectionValue.Exec (projectionStore w record count width label 0 0 out)
      (projectionStore w record count width label 0 0
        (unary true false (guardedValue fields record count width (2+label/2)) ++ out)) t ∧
      t ≤ projectionValueBound w.length record count width label := by
  dsimp only
  let w := fields.flatMap (unary true false)
  let half := label/2
  let rem := label%2
  let slot := 2+half
  let word := unary true false (guardedValue fields record count width slot)
  let frame := projectionStore w record count width label
  have hcopy : (copyProg (14 : Fin 17) 3 11).Exec (frame 0 0 out) (frame label 0 out) (6*label+3) := by
    convert stack_copy (14 : Fin 17) 3 11 (by decide) (by decide) (by decide)
      (frame 0 0 out) rfl using 1 <;>
      first | rfl |
        exact funext (fun k => by simp only [frame, store_eq]; fin_cases k <;> simp) |
        solve | simp [frame, store_eq]
  obtain ⟨u, hu, hub⟩ := extractOn_exec halfPorts (frame label 0 out) label 2 (by decide)
    rfl rfl rfl rfl rfl rfl
  have hhalf : (onPorts halfPorts extract).Exec (frame label 0 out) (frame half rem out) u := by
    convert hu using 1
    exact funext (fun k => by simp only [frame, store_eq]; fin_cases k <;> rfl)
  have hinc := pushSlot_exec w record count width label half rem out
  have hnext := pushSlot_exec w record count width label (half+1) rem out
  rw [show half+1+1=slot by dsimp [slot]; omega] at hnext
  have hseparator := writeSeparator_exec w record count width label slot rem out
  obtain ⟨v, hv, hvb⟩ := guardedRead_exec fields record count width slot (false :: out) hvalid
  have hbit : List.replicate (guardedValue fields record count width slot) true ++ false :: out =
      word ++ out := by simp [word, unary, List.append_assoc]
  rw [hbit] at hv
  have hread : (onPorts (Fin.castAddEmb 3) guardedRead).Exec
      (frame slot rem (false :: out)) (frame slot rem (word ++ out)) v :=
    appendLeft_exec hv (![List.replicate label true, [true,true], List.replicate rem true] :
      Fin 3 → List Bool)
  have hclear : (clearProg (3 : Fin 17)).Exec (frame slot rem (word ++ out))
      (frame 0 rem (word ++ out)) (3*slot+1) := by
    convert clear_exec (3 : Fin 17) (frame slot rem (word ++ out)) using 1 <;>
      first | rfl |
        exact funext (fun k => by simp only [frame, store_eq]; fin_cases k <;> rfl) |
        solve | simp [frame,store_eq]
  have hclearRem : (clearProg (16 : Fin 17)).Exec (frame 0 rem (word ++ out))
      (frame 0 0 (word ++ out)) (3*rem+1) := by
    convert clear_exec (16 : Fin 17) (frame 0 rem (word ++ out)) using 1 <;>
      first | rfl |
        exact funext (fun k => by simp only [frame, store_eq]; fin_cases k <;> rfl) |
        solve | simp [frame,store_eq]
  refine ⟨_, hcopy.seq (hhalf.seq (hinc.seq (hnext.seq (hseparator.seq
    (hread.seq (hclear.seq hclearRem)))))), ?_⟩
  have hle : half ≤ label := Nat.div_le_self _ _
  have hlt : rem < 2 := Nat.mod_lt _ (by decide)
  have hmono : guardedBound w.length record count width slot ≤
      guardedBound w.length record count width (2+label) := by
    unfold guardedBound stepBound
    have hslot : slot ≤ 2+label := Nat.add_le_add_left hle 2
    gcongr
  change v ≤ guardedBound w.length record count width slot at hvb
  change _ ≤ projectionValueBound w.length record count width label
  unfold projectionValueBound
  dsimp only [slot] at *
  omega

/-- The configured emitter writes exactly the projection value used by the lift. -/
theorem emitProjectionAt_exec {q : ℕ} (G : Instance q) (p u v label : ℕ)
    (ha : label < 4*q) (out : List Bool) :
    let e := ordinal p u v
    let w := recordBits G
    ∃ t, emitProjectionValue.Exec (projectionStore w e G.edges.length (2+2*q) label 0 0 out)
      (projectionStore w e G.edges.length (2+2*q) label 0 0
        (unary true false (projectionIndex G p u v label) ++ out)) t ∧
      t ≤ projectionValueBound w.length e G.edges.length (2+2*q) label := by
  let fields := G.edges.flatMap Encoding.edgeWords
  let e := ordinal p u v
  have hlabel : label/2 < 2*q := by omega
  have hvalid (h : e < G.edges.length) : e*(2+2*q)+(2+label/2) < fields.length := by
    change _ < (G.edges.flatMap Encoding.edgeWords).length
    rw [twoToOne_payload_length]
    have hr := Nat.mul_le_mul_right (2+2*q) (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at hr
    omega
  have hv : guardedValue fields e G.edges.length (2+2*q) (2+label/2) =
      projectionIndex G p u v label := by
    by_cases h : e < G.edges.length
    · simp only [guardedValue, e, h, if_pos, projectionIndex, hlabel, dif_pos]
      rw [List.getD_eq_getElem fields 0 (hvalid h)]
      exact twoToOne_projection_get G ⟨e,h⟩ ⟨label/2,hlabel⟩
    · simp [guardedValue, projectionIndex, e, h]
  simpa only [recordBits, hv] using emitProjectionValue_exec fields e G.edges.length
    (2+2*q) label out hvalid

end FourToOneGames.WordMachines.LiftOutput

end

/- LiftCellIndex -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.LiftOutput

open CookPvsNP Radix LiftInput

/-- Positions zero and nine hold the vertex indices. Position eighteen holds the record ordinal. -/
def cellFrame (p u v : ℕ) (left right : Fin 4 → ℕ) (tag : ℕ) : Fin 19 → List Bool :=
  Fin.append (radixStore u p left)
    (Fin.append (radixStore v p right) ![List.replicate tag true])

private def tagPorts : Fin 13 ↪ Fin 19 :=
  ⟨![1,4,5,6,13,14,15,16,2,18,3,8,11], by decide⟩

/-- Decode the left and right indices and compute the record ordinal from the extracted digits. -/
noncomputable def cellIndexMachine : StackProg (Fin 19) Bool :=
  .seq (onPorts (Fin.castAddEmb 10) (decode 3 (by decide)))
    (.seq (onPorts (Fin.natAddEmb 9) (onPorts (Fin.castAddEmb 1) (decode 4 (by decide))))
      (onPorts tagPorts tagMachine))

private theorem digits_lt (n p k : ℕ) (hp : 0 < p) (i : Fin 4) :
    digits n p k i < p := by
  unfold digits
  split
  · exact Nat.mod_lt _ hp
  · exact hp

private theorem tagFrame_exec (p u v : ℕ) (hp : 0 < p) :
    ∃ t, (onPorts tagPorts tagMachine).Exec
      (cellFrame p (u/p^3) (v/p^4) (digits u p 3) (digits v p 4) 0)
      (cellFrame p (u/p^3) (v/p^4) (digits u p 3) (digits v p 4) (ordinal p u v)) t ∧
      t ≤ tagBound p := by
  let x : Fin 3 → ℕ := fun i => digits u p 3 (i.castLE (by decide))
  let y := digits v p 4
  obtain ⟨s, hs, hb⟩ := tagMachine_exec p hp x y
    (fun _ => digits_lt u p 3 hp _) (digits_lt v p 4 hp)
  have ho : tagNumerator x y % p = ordinal p u v := (ordinal_decoded p u v).symm
  rw [ho] at hs
  refine ⟨s, onPorts_exec tagPorts hs ?_ ?_ ?_, hb⟩
  · intro k
    fin_cases k <;> rfl
  · intro k
    fin_cases k <;> rfl
  · intro k hk
    have hlast : k ≠ 18 := fun he => hk 9 (by rw [he]; rfl)
    refine Fin.addCases (m := 9) (n := 10) (fun i _ => ?_) (fun j => ?_) k hlast
    · simp only [cellFrame, Fin.append_left]
    · refine Fin.addCases (m := 9) (n := 1) (fun i _ => ?_) (fun i hi => ?_) j
      · simp only [cellFrame, Fin.append_right, Fin.append_left]
      · fin_cases i
        exact (hi rfl).elim

theorem cellIndexMachine_exec (p u v : ℕ) (hp : 0 < p) :
    ∃ t, cellIndexMachine.Exec (cellFrame p u v (fun _ => 0) (fun _ => 0) 0)
      (cellFrame p (u/p^3) (v/p^4) (digits u p 3) (digits v p 4) (ordinal p u v)) t ∧
      t ≤ 3*(extractBound u p+1) + 4*(extractBound v p+1) + tagBound p + 4 := by
  obtain ⟨a, ha, haB⟩ := decode_exec u p hp 3 (by decide)
  obtain ⟨b, hb, hbB⟩ := decode_exec v p hp 4 (by decide)
  obtain ⟨c, hc, hcB⟩ := tagFrame_exec p u v hp
  have hleft := appendLeft_exec (m := 10) ha
    (Fin.append (radixStore v p (fun _ => 0)) (![[]] : Fin 1 → List Bool))
  have hright := appendRight_exec (n := 9) (appendLeft_exec hb (![[]] : Fin 1 → List Bool))
    (radixStore (u/p^3) p (digits u p 3))
  exact ⟨_, hleft.seq (hright.seq hc), by omega⟩

end FourToOneGames.WordMachines.LiftOutput

end

/- LiftProjectionAtom -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines

/-- Updating a right-hand port leaves the left-hand block unchanged. -/
theorem append_update_right {A : Type} {n m : ℕ} (a : Fin n → A) (b : Fin m → A)
    (i : Fin m) (value : A) :
    Function.update (Fin.append a b) (Fin.natAdd n i) value =
      Fin.append a (Function.update b i value) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · have hne : j.castAdd m ≠ i.natAdd n := by
      intro h
      have he : j.val = n+i.val := congrArg Fin.val h
      omega
    simp only [Function.update_of_ne hne, Fin.append_left]
  · by_cases hj : j = i
    · subst j
      simp only [Function.update_self, Fin.append_right]
    · have hne : j.natAdd n ≠ i.natAdd n := by
        intro h
        have he : n+j.val = n+i.val := congrArg Fin.val h
        exact hj (Fin.ext (by omega))
      simp only [Function.update_of_ne hne, Function.update_of_ne hj, Fin.append_right]

/-- Copy a preserved input into a working block and leave its scratch tape empty. -/
theorem copyAppendRight_exec {A : Type} {n m : ℕ} (left : Fin n → List A) (right : Fin m → List A)
    (src : Fin n) (dst scratch : Fin m) (hds : dst ≠ scratch) (hw : right scratch = []) :
    (CookPvsNP.copyProg (src.castAdd m) (dst.natAdd n) (scratch.natAdd n)).Exec
      (Fin.append left right) (Fin.append left (Function.update right dst (left src ++ right dst)))
      (6*(left src).length+3) := by
  have hsd : src.castAdd m ≠ dst.natAdd n := by
    intro he
    have hi : src.val = n+dst.val := congrArg Fin.val he
    omega
  have hsw : src.castAdd m ≠ scratch.natAdd n := by
    intro he
    have hi : src.val = n+scratch.val := congrArg Fin.val he
    omega
  have hdw : dst.natAdd n ≠ scratch.natAdd n := by
    intro he
    have hi : n+dst.val = n+scratch.val := congrArg Fin.val he
    exact hds (Fin.ext (by omega))
  have hs : Fin.append left right (scratch.natAdd n) = [] := by
    simpa only [Fin.append_right] using hw
  simpa only [Fin.append_left, Fin.append_right, append_update_right] using
    CookPvsNP.stack_copy (src.castAdd m) (dst.natAdd n) (scratch.natAdd n) hsd hsw hdw
      (Fin.append left right) hs

namespace LiftOutput

open CookPvsNP OAI.PerfectCompleteness LiftInput Radix

def projectionStart {q : ℕ} (G : Instance q) (p u v a : ℕ) (tail : List Bool) : Fin 36 → List Bool :=
  Fin.append (cellFrame p u v (fun _ => 0) (fun _ => 0) 0)
    (projectionStore (recordBits G) 0 G.edges.length (2+2*q) a 0 0 tail)

def decodedCell {q : ℕ} (G : Instance q) (p u v a : ℕ) (tail : List Bool) : Fin 36 → List Bool :=
  let e := ordinal p u v
  Fin.append (cellFrame p (u/p^3) (v/p^4) (digits u p 3) (digits v p 4) e)
    (projectionStore (recordBits G) e G.edges.length (2+2*q) a 0 0 tail)

/-- Decode a pair of copied vertices and append its projection entry to the front of the output. -/
noncomputable def projectionAtom : StackProg (Fin 36) Bool :=
  .seq (onPorts (Fin.castAddEmb 17) cellIndexMachine)
    (.seq (copyProg 18 20 30) (onPorts (Fin.natAddEmb 19) emitProjectionValue))

def projectionAtomBound (n count q p u v a : ℕ) : ℕ :=
  3*(extractBound u p+1) + 4*(extractBound v p+1) + tagBound p +
    6*p + projectionValueBound n p count (2+2*q) a + 9

private theorem projectionStore_setRecord (w : List Bool) (e count width a : ℕ) (out : List Bool) :
    Function.update (projectionStore w 0 count width a 0 0 out) 1 (List.replicate e true) =
      projectionStore w e count width a 0 0 out := by
  funext k
  fin_cases k <;> rfl

private theorem copyOrdinal_exec {q : ℕ} (G : Instance q) (p u v a : ℕ) (tail : List Bool) :
    let e := ordinal p u v
    (copyProg (18 : Fin 36) 20 30).Exec
      (Fin.append (cellFrame p (u/p^3) (v/p^4) (digits u p 3) (digits v p 4) e)
        (projectionStore (recordBits G) 0 G.edges.length (2+2*q) a 0 0 tail))
      (decodedCell G p u v a tail) (6*e+3) := by
  let e := ordinal p u v
  let cell := cellFrame p (u/p^3) (v/p^4) (digits u p 3) (digits v p 4) e
  let right := projectionStore (recordBits G) 0 G.edges.length (2+2*q) a 0 0 tail
  let input := Fin.append cell right
  have hsrc : input 18 = List.replicate e true := rfl
  have hd : input 20 = [] := rfl
  have hcopy := stack_copy (18 : Fin 36) 20 30 (by decide) (by decide) (by decide) input rfl
  have hupdate : Function.update input 20 (List.replicate e true) = decodedCell G p u v a tail := by
    change Function.update (Fin.append cell right) (Fin.natAdd 19 (1 : Fin 17))
      (List.replicate e true) = _
    rw [append_update_right]
    exact congrArg (Fin.append cell) (projectionStore_setRecord (recordBits G) e G.edges.length
      (2+2*q) a tail)
  simpa only [hsrc, hd, List.length_replicate, List.append_nil, hupdate] using hcopy

theorem projectionAtom_exec {q : ℕ} (G : Instance q) (p u v a : ℕ) (hp : 0 < p)
    (ha : a < 4*q) (tail : List Bool) :
    ∃ t, projectionAtom.Exec (projectionStart G p u v a tail)
      (decodedCell G p u v a (unary true false (projectionIndex G p u v a) ++ tail)) t ∧
      t ≤ projectionAtomBound (recordBits G).length G.edges.length q p u v a := by
  let e := ordinal p u v
  let cell := cellFrame p (u/p^3) (v/p^4) (digits u p 3) (digits v p 4) e
  obtain ⟨t, ht, htb⟩ := cellIndexMachine_exec p u v hp
  obtain ⟨s, hs, hsb⟩ := emitProjectionAt_exec G p u v a ha tail
  have hleft := appendLeft_exec ht (projectionStore (recordBits G) 0 G.edges.length
    (2+2*q) a 0 0 tail)
  have hright := appendRight_exec hs cell
  refine ⟨_, hleft.seq ((copyOrdinal_exec G p u v a tail).seq hright), ?_⟩
  have he : e ≤ p := (Nat.mod_lt _ hp).le
  have hm : projectionValueBound (recordBits G).length e G.edges.length (2+2*q) a ≤
      projectionValueBound (recordBits G).length p G.edges.length (2+2*q) a := by
    unfold projectionValueBound RecordLookup.guardedBound RecordLookup.stepBound
    gcongr
  change s ≤ projectionValueBound (recordBits G).length e G.edges.length (2+2*q) a at hsb
  unfold projectionAtomBound
  omega

end LiftOutput
end FourToOneGames.WordMachines

end

/- BankCalls -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.BankCalls

open CookPvsNP LiftInput

private noncomputable def nonemptyBank {m : ℕ} {A : Type} (h : Fin m → Option A) : Bool := by
  classical
  exact decide (∃ k, (h k).isSome = true)

private def clearStep {m : ℕ} {A : Type} : StackProg (Fin m) A :=
  .act (fun _ _ => .pop)

/-- Empty a work bank by popping all of its stacks in parallel. -/
noncomputable def clearBank (m : ℕ) (A : Type) : StackProg (Fin m) A :=
  .loop nonemptyBank clearStep

theorem clearBank_exec {m : ℕ} {A : Type} (bank : Fin m → List A) (cap : ℕ)
    (hb : ∀ k, (bank k).length ≤ cap) :
    ∃ t, (clearBank m A).Exec bank (fun _ => []) t ∧ t ≤ 3*cap+1 := by
  have hempty : (clearBank m A).Exec (fun _ => []) (fun _ => []) 1 :=
    StackProg.Exec.loopFalse (test := nonemptyBank) (p := clearStep) (by simp [nonemptyBank])
  induction cap generalizing bank with
  | zero =>
      have he : bank = fun _ => [] := funext (fun k => List.length_eq_zero_iff.mp (Nat.le_zero.mp (hb k)))
      exact ⟨1, he.symm ▸ hempty, by omega⟩
  | succ cap ih =>
      classical
      by_cases h : ∀ k, bank k = []
      · have he : bank = fun _ => [] := funext h
        exact ⟨1, he.symm ▸ hempty, by omega⟩
      · have hx : ∃ k, bank k ≠ [] := not_forall.mp h
        obtain ⟨k, hk⟩ := hx
        have hguard : nonemptyBank (fun j => (bank j).head?) = true := by
          simp only [nonemptyBank, decide_eq_true_eq]
          exact ⟨k, by cases he : bank k <;> simp_all⟩
        let tail := fun k => (bank k).tail
        have hs : clearStep.Exec bank tail 1 := StackProg.Exec.act (fun _ _ => .pop) bank
        have hcap : ∀ k, (tail k).length ≤ cap := by
          intro k
          simp only [tail, List.length_tail]
          have hlen := hb k
          omega
        obtain ⟨t, ht, htb⟩ := ih tail hcap
        exact ⟨_, StackProg.Exec.loopTrue (test := nonemptyBank) hguard hs ht, by omega⟩

theorem append_update_left {A : Type} {n m : ℕ} (left : Fin n → A) (right : Fin m → A)
    (i : Fin n) (v : A) :
    Function.update (Fin.append left right) (i.castAdd m) v =
      Fin.append (Function.update left i v) right := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · by_cases hj : j = i
    · subst j
      simp only [Function.update_self, Fin.append_left]
    · have hne : j.castAdd m ≠ i.castAdd m := fun he => hj (Fin.ext (congrArg (fun k : Fin (n+m) => k.val) he))
      simp only [Function.update_of_ne hne, Function.update_of_ne hj, Fin.append_left]
  · have hne : j.natAdd n ≠ i.castAdd m := by
      intro he
      have hv : n+j.val = i.val := congrArg Fin.val he
      omega
    simp only [Function.update_of_ne hne, Fin.append_right]

private def loadOne {n m : ℕ} {A : Type} (scratch : Fin n) (pair : Fin n × Fin m) :
    StackProg (Fin (n+m)) A :=
  copyProg (pair.1.castAdd m) (pair.2.natAdd n) (scratch.castAdd m)

private theorem loadOne_exec {n m : ℕ} {A : Type} (parent : Fin n → List A) (bank : Fin m → List A)
    (scratch src : Fin n) (dst : Fin m) (hne : src ≠ scratch) (hw : parent scratch = []) :
    (loadOne scratch (src,dst)).Exec (Fin.append parent bank)
      (Fin.append parent (Function.update bank dst (parent src ++ bank dst)))
      (6*(parent src).length+3) := by
  have hsd : src.castAdd m ≠ dst.natAdd n := by
    intro he
    have hv : src.val = n+dst.val := congrArg Fin.val he
    omega
  have hsw : src.castAdd m ≠ scratch.castAdd m :=
    fun he => hne (Fin.ext (congrArg (fun k : Fin (n+m) => k.val) he))
  have hdw : dst.natAdd n ≠ scratch.castAdd m := by
    intro he
    have hv : n+dst.val = scratch.val := congrArg Fin.val he
    omega
  have he := stack_copy (src.castAdd m) (dst.natAdd n) (scratch.castAdd m) hsd hsw hdw
    (Fin.append parent bank) (by simpa only [Fin.append_left] using hw)
  simpa only [loadOne, Fin.append_left, Fin.append_right, append_update_right] using he

def loadInputs {n m : ℕ} {A : Type} (scratch : Fin n) :
    List (Fin n × Fin m) → StackProg (Fin (n+m)) A
  | [] => .act (fun _ _ => .keep)
  | sd::rest => .seq (loadOne scratch sd) (loadInputs scratch rest)

def copiedInputs {n m : ℕ} {A : Type} (parent : Fin n → List A)
    (inputs : List (Fin n × Fin m)) (bank : Fin m → List A) : Fin m → List A :=
  inputs.foldl (fun saved sd => Function.update saved sd.2 (parent sd.1 ++ saved sd.2)) bank

def copyCost {n m : ℕ} {A : Type} (parent : Fin n → List A) : List (Fin n × Fin m) → ℕ
  | [] => 1
  | sd::rest => 6*(parent sd.1).length+3+1+copyCost parent rest

theorem copyCost_le {n m : ℕ} {A : Type} (parent : Fin n → List A)
    (inputs : List (Fin n × Fin m)) (cap : ℕ) (h : ∀ sd ∈ inputs, (parent sd.1).length ≤ cap) :
    copyCost parent inputs ≤ inputs.length*(6*cap+4)+1 := by
  induction inputs with
  | nil => simp [copyCost]
  | cons sd rest ih =>
      have hb := h sd (List.mem_cons_self)
      have hr := ih (fun pair hp => h pair (List.mem_cons_of_mem _ hp))
      simp only [copyCost, List.length_cons, Nat.succ_mul] at hr ⊢
      omega

theorem loadInputs_exec {n m : ℕ} {A : Type} (parent : Fin n → List A) (bank : Fin m → List A)
    (scratch : Fin n) (inputs : List (Fin n × Fin m)) (hw : parent scratch = [])
    (hne : ∀ sd ∈ inputs, sd.1 ≠ scratch) :
    (loadInputs scratch inputs).Exec (Fin.append parent bank)
      (Fin.append parent (copiedInputs parent inputs bank)) (copyCost parent inputs) := by
  induction inputs generalizing bank with
  | nil => exact StackProg.Exec.act (fun _ _ => .keep) _
  | cons sd rest ih =>
      exact (loadOne_exec parent bank scratch sd.1 sd.2 (hne sd List.mem_cons_self) hw).seq
        (ih _ (fun pair hp => hne pair (List.mem_cons_of_mem _ hp)))

private def prependResult {n m : ℕ} {A : Type} (scratch out : Fin n) (result : Fin m) :
    StackProg (Fin (n+m)) A :=
  copyProg (result.natAdd n) (out.castAdd m) (scratch.castAdd m)

private theorem prependResult_exec {n m : ℕ} {A : Type} (parent : Fin n → List A)
    (bank : Fin m → List A) (scratch out : Fin n) (result : Fin m)
    (hw : parent scratch = []) (hne : out ≠ scratch) :
    (prependResult scratch out result).Exec (Fin.append parent bank)
      (Fin.append (Function.update parent out (bank result ++ parent out)) bank)
      (6*(bank result).length+3) := by
  have hs (port : Fin n) : result.natAdd n ≠ port.castAdd m := by
    intro he
    have hv : n+result.val = port.val := congrArg Fin.val he
    omega
  have hne' : out.castAdd m ≠ scratch.castAdd m :=
    fun he => hne (Fin.ext (congrArg (fun k : Fin (n+m) => k.val) he))
  have h := stack_copy (result.natAdd n) (out.castAdd m) (scratch.castAdd m)
    (hs out) (hs scratch) hne' (Fin.append parent bank) (by simpa only [Fin.append_left] using hw)
  simpa only [prependResult, Fin.append_left, Fin.append_right, append_update_left] using h

/-- Give a subprogram private copies of its operands, prepend its result, and reset the bank. -/
noncomputable def callBank {n m : ℕ} {A : Type} (scratch out : Fin n) (result : Fin m)
    (inputs : List (Fin n × Fin m)) (body : StackProg (Fin m) A) : StackProg (Fin (n+m)) A :=
  .seq (loadInputs scratch inputs) (.seq (onPorts (Fin.natAddEmb n) body)
    (.seq (prependResult scratch out result) (onPorts (Fin.natAddEmb n) (clearBank m A))))

theorem callBank_exec {n m : ℕ} {A : Type} (parent : Fin n → List A)
    (scratch out : Fin n) (result : Fin m) (inputs : List (Fin n × Fin m))
    (body : StackProg (Fin m) A) (bankEnd : Fin m → List A) (word : List A) (t budget : ℕ)
    (hw : parent scratch = []) (hne : out ≠ scratch) (hinputs : ∀ p ∈ inputs, p.1 ≠ scratch)
    (hrun : body.Exec (copiedInputs parent inputs (fun _ => [])) bankEnd t)
    (hword : bankEnd result = word) (ht : t ≤ budget) :
    ∃ u, (callBank scratch out result inputs body).Exec (Fin.append parent (fun _ => []))
      (Fin.append (Function.update parent out (word ++ parent out)) (fun _ => [])) u ∧
      u ≤ 10*copyCost parent inputs + 10*budget + 7 := by
  let next := Function.update parent out (word ++ parent out)
  have hload := loadInputs_exec parent (fun _ => []) scratch inputs hw hinputs
  have hsub := appendRight_exec hrun parent
  have hp := prependResult_exec parent bankEnd scratch out result hw hne
  rw [hword] at hp
  have hend (k : Fin m) : (bankEnd k).length ≤ copyCost parent inputs + budget := by
    have hinput := StackTM2Trace.Exec_store_length_le hload (k.natAdd n)
    simp only [Fin.append_right, List.length_nil, Nat.zero_add] at hinput
    exact (StackTM2Trace.Exec_store_length_le hrun k).trans (Nat.add_le_add hinput ht)
  obtain ⟨v, hv, hvb⟩ := clearBank_exec bankEnd (copyCost parent inputs+budget) hend
  have hfinal := appendRight_exec hv next
  refine ⟨_, hload.seq (hsub.seq (hp.seq hfinal)), ?_⟩
  have hs := hend result
  rw [hword] at hs
  omega

end FourToOneGames.WordMachines.BankCalls

end

/- SATVariableName -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity
open WordMachines WordMachines.UnaryPair WordMachines.BankCalls
open WordMachines.LiftInput (appendLeft_exec)

private noncomputable def nativePair : StackProg (Fin 8) BSym :=
  StackProgAlphabet.mapProg nativeBit fromNativeBit pairMachine

private def nativePairStore (a b out : ℕ) : Fin 8 → List BSym :=
  ![List.replicate a .one, List.replicate b .one, List.replicate out .one, [], [], [], [], []]

private theorem nativePair_exec (a b : ℕ) :
    ∃ t, nativePair.Exec (nativePairStore a b 0) (nativePairStore a b (Nat.pair a b)) t ∧
      t ≤ pairBound (a+b) := by
  obtain ⟨t, ht, hb⟩ := pairMachine_exec a b []
  have hinv : Function.LeftInverse fromNativeBit nativeBit := by
    intro bit
    cases bit <;> rfl
  have hn := StackProgAlphabet.mapProg_exec nativeBit fromNativeBit hinv ht
  refine ⟨t, ?_, hb⟩
  have hs (out : ℕ) : StackProgAlphabet.mapStore nativeBit
      (inputStore a b (List.replicate out true ++ [])) = nativePairStore a b out := by
    funext k
    simp only [List.append_nil]
    fin_cases k <;>
      first
      | rfl
      | change (List.replicate _ true).map nativeBit = List.replicate _ BSym.one
        simp [nativeBit]
  have hs0 : StackProgAlphabet.mapStore nativeBit (inputStore a b []) =
      nativePairStore a b 0 := hs 0
  rw [hs0, hs] at hn
  exact hn

private def pairInputs (x y : Fin 8) : List (Fin 8 × Fin 8) := [(x,0),(y,1)]

def pairPassBound (n : ℕ) : ℕ := 10*(6*n+9) + 10*pairBound n+7

/-- Run the unary pairing machine in a cleaned work bank and prepend its result. -/
noncomputable def pairPass (x y dest : Fin 8) : StackProg (Fin 16) BSym :=
  callBank 7 dest 2 (pairInputs x y) nativePair

theorem pairPass_exec (p : Fin 8 → List BSym) (x y dest : Fin 8) (a b : ℕ)
    (hx : p x = List.replicate a .one) (hy : p y = List.replicate b .one)
    (hw : p 7 = []) (hxw : x ≠ 7) (hyw : y ≠ 7) (hdw : dest ≠ 7) :
    ∃ t, (pairPass x y dest).Exec (Fin.append p (fun _ : Fin 8 => []))
      (Fin.append (Function.update p dest (List.replicate (Nat.pair a b) .one ++ p dest))
        (fun _ : Fin 8 => [])) t ∧
      t ≤ pairPassBound (a+b) := by
  obtain ⟨t, ht, hb⟩ := nativePair_exec a b
  have hinput : copiedInputs p (pairInputs x y) (fun _ => []) = nativePairStore a b 0 := by
    funext k
    fin_cases k <;> simp [copiedInputs, pairInputs, hx, hy, nativePairStore]
  obtain ⟨u, hu, hub⟩ := callBank_exec p 7 dest 2 (pairInputs x y)
    nativePair (nativePairStore a b (Nat.pair a b)) (List.replicate (Nat.pair a b) .one)
    t (pairBound (a+b)) hw hdw (by simp [pairInputs, hxw, hyw]) (by rw [hinput]; exact ht)
    rfl hb
  refine ⟨u, hu, ?_⟩
  simp only [pairInputs, copyCost, hx, hy, List.length_replicate] at hub
  unfold pairPassBound
  omega

private def nameParent (side vertex gate label : ℕ) (first second out : List BSym) :
    Fin 8 → List BSym :=
  ![List.replicate side .one, List.replicate vertex .one, List.replicate gate .one,
    List.replicate label .one, first, second, out, []]

def nameStore (side vertex gate label : ℕ) (out : List BSym) : Fin 16 → List BSym :=
  Fin.append (nameParent side vertex gate label [] [] out) (fun _ : Fin 8 => [])

private noncomputable def clearNameWork : StackProg (Fin 16) BSym :=
  onPorts (Fin.castAddEmb 8) ((clearProg (4 : Fin 8)).seq (clearProg 5))

/-- Prepend the nested-pair variable name in unary and preserve its four fields. -/
noncomputable def variableName : StackProg (Fin 16) BSym :=
  .seq (pairPass 2 3 4) (.seq (pairPass 1 4 5) (.seq (pairPass 0 5 6) clearNameWork))

def variableNameBound (side vertex gate label : ℕ) : ℕ :=
  let a := Nat.pair gate label
  let b := Nat.pair vertex a
  pairPassBound (gate+label) + pairPassBound (vertex+a) + pairPassBound (side+b) + 3*(a+b)+6

theorem variableName_exec (side vertex gate label : ℕ) (out : List BSym) :
    ∃ t, variableName.Exec (nameStore side vertex gate label out)
      (nameStore side vertex gate label
        (List.replicate (Nat.pair side (Nat.pair vertex (Nat.pair gate label))) .one ++ out)) t ∧
      t ≤ variableNameBound side vertex gate label := by
  let a := Nat.pair gate label
  let b := Nat.pair vertex a
  let wa := List.replicate a BSym.one
  let wb := List.replicate b BSym.one
  let w := List.replicate (Nat.pair side b) BSym.one ++ out
  let parent := nameParent side vertex gate label
  obtain ⟨t₁, h₁, ht₁⟩ := pairPass_exec (parent [] [] out) 2 3 4 gate label
    rfl rfl rfl (by decide) (by decide) (by decide)
  have e₁ : Function.update (parent [] [] out) 4
      (wa ++ parent [] [] out 4) = parent wa [] out := by
    refine funext fun k => ?_
    fin_cases k <;> simp [parent, nameParent]
  change (pairPass 2 3 4).Exec _
    (Fin.append (Function.update (parent [] [] out) 4 (wa ++ parent [] [] out 4))
      (fun _ : Fin 8 => [])) _ at h₁
  rw [e₁] at h₁
  obtain ⟨t₂, h₂, ht₂⟩ := pairPass_exec (parent wa [] out) 1 4 5 vertex a
    rfl rfl rfl (by decide) (by decide) (by decide)
  have e₂ : Function.update (parent wa [] out) 5
      (wb ++ parent wa [] out 5) = parent wa wb out := by
    refine funext fun k => ?_
    fin_cases k <;> simp [parent, nameParent]
  change (pairPass 1 4 5).Exec _
    (Fin.append (Function.update (parent wa [] out) 5 (wb ++ parent wa [] out 5))
      (fun _ : Fin 8 => [])) _ at h₂
  rw [e₂] at h₂
  obtain ⟨t₃, h₃, ht₃⟩ := pairPass_exec (parent wa wb out) 0 5 6 side b
    rfl rfl rfl (by decide) (by decide) (by decide)
  have e₃ : Function.update (parent wa wb out) 6 w = parent wa wb w := by
    refine funext fun k => ?_
    fin_cases k <;> rfl
  change (pairPass 0 5 6).Exec _
    (Fin.append (Function.update (parent wa wb out) 6 w) (fun _ : Fin 8 => [])) _ at h₃
  rw [e₃] at h₃
  have h₄ : (clearProg (4 : Fin 8)).Exec (parent wa wb w) (parent [] wb w) (3*a+1) := by
    convert clear_exec (4 : Fin 8) (parent wa wb w) using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl) | simp [parent, nameParent, wa]
  have h₅ : (clearProg (5 : Fin 8)).Exec (parent [] wb w) (parent [] [] w) (3*b+1) := by
    convert clear_exec (5 : Fin 8) (parent [] wb w) using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl) | simp [parent, nameParent, wb]
  have hc : clearNameWork.Exec (Fin.append (parent wa wb w) (fun _ : Fin 8 => []))
      (Fin.append (parent [] [] w) (fun _ : Fin 8 => [])) _ := appendLeft_exec (h₄.seq h₅) (fun _ => [])
  refine ⟨_, h₁.seq (h₂.seq (h₃.seq hc)), ?_⟩
  change _ ≤ pairPassBound (gate+label) + pairPassBound (vertex+a) +
    pairPassBound (side+b) + 3*(a+b)+6
  omega

private theorem pair_le_square {a b n : ℕ} (h : a+b ≤ n) : Nat.pair a b ≤ (n+1)^2 := by
  have hm : max a b ≤ n := max_le (by omega) (by omega)
  refine (Nat.pair_lt_max_add_one_sq a b).le.trans ?_
  gcongr

private theorem pairPassBound_mono {n m : ℕ} (h : n ≤ m) :
    pairPassBound n ≤ pairPassBound m := by
  unfold pairPassBound pairBound
  gcongr

def variableNameCap (n : ℕ) : ℕ := n + (n + (n+1)^2 + 1)^2

theorem variableNameBound_le (side vertex gate label n : ℕ) (h : side+vertex+gate+label ≤ n) :
    let cap := variableNameCap n
    variableNameBound side vertex gate label ≤ 3*pairPassBound cap+6*cap+6 := by
  dsimp only
  let a := Nat.pair gate label
  let b := Nat.pair vertex a
  let cap := variableNameCap n
  have ha : a ≤ (n+1)^2 := pair_le_square (by omega)
  have hb : b ≤ (n + (n+1)^2 + 1)^2 := pair_le_square (by omega)
  have hab : a ≤ b := Nat.right_le_pair vertex a
  have h₁ : gate+label ≤ cap := by unfold cap variableNameCap; omega
  have h₂ : vertex+a ≤ cap := by unfold cap variableNameCap; omega
  have h₃ : side+b ≤ cap := by unfold cap variableNameCap; omega
  have h₄ : b ≤ cap := by omega
  have h₅ := pairPassBound_mono h₁
  have h₆ := pairPassBound_mono h₂
  have h₇ := pairPassBound_mono h₃
  change pairPassBound (gate+label) + pairPassBound (vertex+a) + pairPassBound (side+b) +
    3*(a+b)+6 ≤ 3*pairPassBound cap+6*cap+6
  omega

end FourToOneGames.SATMachine

end

/- BinarySATFraming -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open CLRS.Chapter34.Turing.PolyBuilder
open OAI.PerfectCompleteness.BinaryFormula
open ProjSchedTW.Complexity

/-- A clause marker and signed, little-endian numeral words. -/
def literalWord (l : Literal) : List BSym :=
  (if l.positive then BSym.one else .zero) :: encNat l.name

def clauseWord (c : Clause) : List BSym :=
  .minus :: (literalWord (c.get 0) ++ literalWord (c.get 1) ++ literalWord (c.get 2))

def formulaWord (f : Formula) : List BSym :=
  f.clauses.flatMap clauseWord

/-- True mode expects a sign or clause marker. False mode expects a name digit. -/
def framingSpec : StatefulFlatMapSpec Bool BSym Bool where
  initial := true
  action start t :=
    if start then
      match t with
      | .minus => ([true], true)
      | .one => ([true], false)
      | .zero => ([false], false)
      | .sep => ([], true)
    else
      match t with
      | .one => ([true, true], false)
      | .zero => ([true, false], false)
      | .sep => ([false], true)
      | .minus => ([], true)
  finish _ := [false]

abbrev frameFrom := rewriteStatefulFlatMapFrom framingSpec

private theorem frameName (bs : List Bool) (tail : List BSym) :
    frameFrom false ((bs.map (fun b => if b then BSym.one else .zero)) ++ .sep :: tail) =
      (bs.flatMap fun b => [true, b]) ++ false :: frameFrom true tail := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simpa [frameFrom, rewriteStatefulFlatMapFrom, framingSpec] using ih

private theorem frameLiteral (l : Literal) (tail : List BSym) :
    frameFrom true (literalWord l ++ tail) =
      l.positive :: ((l.name.bits.flatMap fun b => [true, b]) ++ false :: frameFrom true tail) := by
  cases h : l.positive <;>
    simpa [literalWord, encNat, h, frameFrom, rewriteStatefulFlatMapFrom, framingSpec,
      List.append_assoc] using
      congrArg (List.cons l.positive) (frameName l.name.bits tail)

private def clauseBits (c : Clause) : List Bool :=
  let lit := fun l : Literal => l.positive :: ((l.name.bits.flatMap fun b => [true, b]) ++ [false])
  true :: (lit (c.get 0) ++ lit (c.get 1) ++ lit (c.get 2))

private theorem frameClause (c : Clause) (tail : List BSym) :
    frameFrom true (clauseWord c ++ tail) = clauseBits c ++ frameFrom true tail := by
  simp only [clauseWord, List.cons_append, List.append_assoc]
  change true :: frameFrom true
    (literalWord (c.get 0) ++ (literalWord (c.get 1) ++ (literalWord (c.get 2) ++ tail))) = _
  rw [frameLiteral, frameLiteral, frameLiteral]
  simp [clauseBits, List.append_assoc]

private theorem frameClauses (cs : List Clause) :
    frameFrom true (cs.flatMap clauseWord) = cs.flatMap clauseBits ++ [false] := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.flatMap_cons, frameClause, ih, List.append_assoc]

theorem framing_correct (f : Formula) :
    rewriteStatefulFlatMap framingSpec (formulaWord f) = serializeFormula f := by
  exact frameClauses f.clauses

/-- A polynomial-time certificate for the final binary 3SAT framing pass. -/
noncomputable def framing_polytime :
    Turing.TM2ComputableInPolyTime formulaWord id serializeFormula where
  tm := (statefulFlatMap_computableInPolyTime framingSpec).tm
  inputAlphabet := (statefulFlatMap_computableInPolyTime framingSpec).inputAlphabet
  outputAlphabet := (statefulFlatMap_computableInPolyTime framingSpec).outputAlphabet
  time := (statefulFlatMap_computableInPolyTime framingSpec).time
  outputsFun f := by
    simpa only [framing_correct, id_eq] using
      (statefulFlatMap_computableInPolyTime framingSpec).outputsFun (formulaWord f)


theorem binaryInput_polytime_of_formula
    (h : Turing.TM2ComputableInPolyTime encodeLabelCover formulaWord satFormula) :
    Nonempty (Turing.TM2ComputableInPolyTime encodeLabelCover (id : List Bool → List Bool)
      binaryInput) := by
  exact Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch h framing_polytime


open CookPvsNP hiding Literal
open FourToOneGames.WordMachines (onPorts onPorts_exec)

private def signSymbol (l : Literal) : BSym := if l.positive then .one else .zero

def unaryLiteralWord (l : Literal) : List BSym :=
  signSymbol l :: List.replicate l.name .one

local instance : Inhabited BSym := ⟨.zero⟩
private def writerPorts : Fin 5 ↪ Fin 6 := ⟨![0,1,2,3,4], by decide⟩

private def saveSign : StackProg (Fin 6) BSym :=
  .act (transferAct 0 (fun k => decide (k = 5)))

/-- Convert a sign and unary name to the native binary literal stream. -/
theorem unaryLiteral_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime unaryLiteralWord id literalWord) := by
  obtain ⟨writer, C, hwriter⟩ := unary_to_encNat_stack
  let emitSign : StackProg (Fin 6) BSym := transferProg (5 : Fin 6) (fun k => decide (k = 1))
  let prog := saveSign.seq ((onPorts writerPorts writer).seq emitSign)
  refine ⟨StackTM2Time.programPolytime unaryLiteralWord id literalWord prog 0 1
    (Polynomial.C C * Polynomial.X ^ 2 + 7) ?_⟩
  intro l
  let s0 := (prog.machine.init 0 (unaryLiteralWord l)).store
  let s1 : Fin 6 → List BSym := ![List.replicate l.name .one, [], [], [], [], [signSymbol l]]
  let s2 : Fin 6 → List BSym := ![List.replicate l.name .one, encNat l.name, [], [], [], [signSymbol l]]
  let s3 : Fin 6 → List BSym := ![List.replicate l.name .one, literalWord l, [], [], [], []]
  have ha : saveSign.Exec s0 s1 1 := by
    unfold saveSign
    convert StackProg.Exec.act _ s0 using 1
    exact funext (fun k => by
      fin_cases k <;> simp [s0, s1, StackMachine.init, StackProg.applyAct, transferAct,
        StackAct.apply, unaryLiteralWord])
  obtain ⟨n, hn, hb⟩ := hwriter l.name []
  have hw : (onPorts writerPorts writer).Exec s1 s2 n := by
    refine onPorts_exec writerPorts hn ?_ ?_ ?_
    · intro k
      fin_cases k <;> rfl
    · intro k
      fin_cases k <;> simp [s2, writerPorts]
    · intro k hk
      fin_cases k
      · exact (hk 0 rfl).elim
      · exact (hk 1 rfl).elim
      · rfl
      · rfl
      · rfl
      · rfl
  have he : emitSign.Exec s2 s3 4 := by
    unfold emitSign
    convert stack_transfer (5 : Fin 6) (fun k => decide (k = 1)) s2 using 1 <;>
      first | rfl | exact funext (fun k => by
        fin_cases k <;> simp [s2, s3, transferStore, literalWord, signSymbol])
  refine ⟨s3, _, ha.seq (hw.seq he), rfl, ?_⟩
  simp [unaryLiteralWord]
  omega

end FourToOneGames.SATMachine

end

/- SATNamedLiteral -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity WordMachines
open WordMachines.LiftInput (appendLeft_exec)

private def numeralWriterPorts : Fin 5 ↪ Fin 20 := ⟨![6,16,17,18,19], by decide⟩

private def literalState (s v g i : ℕ) (name out : List BSym) : Fin 20 → List BSym :=
  Fin.append (nameStore s v g i name) (![out,[],[],[]] : Fin 4 → List BSym)

def literalStore (s v g i : ℕ) (out : List BSym) : Fin 20 → List BSym :=
  literalState s v g i [] out

def signBit (positive : Bool) : BSym := if positive then .one else .zero

def literalIndex (s v g i : ℕ) : ℕ := Nat.pair s (Nat.pair v (Nat.pair g i))

def namedLiteralWord (s v g i : ℕ) (positive : Bool) : List BSym :=
  signBit positive :: encNat (literalIndex s v g i)

private theorem pair_le_cap {a b n : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    Nat.pair a b ≤ (n+1)^2 :=
  (Nat.pair_lt_max_add_one_sq a b).le.trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le ha hb) 1) 2)

theorem literalIndex_le (s v g i cap : ℕ) (h : s+v+g+i ≤ cap) :
    literalIndex s v g i ≤ (variableNameCap cap+1)^2 := by
  unfold literalIndex variableNameCap
  have hgi := pair_le_cap (a := g) (b := i) (n := cap) (by omega) (by omega)
  have hvi := pair_le_cap (a := v) (b := Nat.pair g i) (n := cap+(cap+1)^2)
    (by omega) (by omega)
  exact pair_le_cap (by omega) (by omega)

/-- Write a signed binary variable name using unary input fields. -/
noncomputable def namedLiteral (writer : StackProg (Fin 5) BSym) (positive : Bool) :
    StackProg (Fin 20) BSym :=
  .seq (onPorts (Fin.castAddEmb 4) variableName)
    (.seq (onPorts numeralWriterPorts writer) (.seq (clearProg 6) (pushProg 16 (signBit positive))))

def IsNumeralWriter (writer : StackProg (Fin 5) BSym) (C : ℕ) : Prop :=
  ∀ (n : ℕ) (tail : List BSym), ∃ steps,
    writer.Exec
      (fun k ↦ if k = 0 then List.replicate n .one else if k = 1 then tail else [])
      (fun k ↦ if k = 0 then List.replicate n .one else if k = 1 then encNat n ++ tail else []) steps ∧
    steps ≤ C*(n+1)^2

theorem exists_numeralWriter : ∃ (writer : StackProg (Fin 5) BSym) (C : ℕ),
    IsNumeralWriter writer C := unary_to_encNat_stack

set_option maxHeartbeats 3000000 in
theorem namedLiteral_exec (writer : StackProg (Fin 5) BSym) (C : ℕ)
    (hw : IsNumeralWriter writer C)
    (s v g i : ℕ) (positive : Bool) (out : List BSym) :
    let n := Nat.pair s (Nat.pair v (Nat.pair g i))
    ∃ t, (namedLiteral writer positive).Exec (literalStore s v g i out)
      (literalStore s v g i (signBit positive :: (encNat n ++ out))) t ∧
      t ≤ variableNameBound s v g i + C*(n+1)^2 + 3*n+5 := by
  dsimp only
  let n := Nat.pair s (Nat.pair v (Nat.pair g i))
  let unary := List.replicate n BSym.one
  let tail := encNat n ++ out
  obtain ⟨a, ha, hab⟩ := variableName_exec s v g i []
  have ha' : (onPorts (Fin.castAddEmb 4) variableName).Exec (literalStore s v g i out)
      (literalState s v g i unary out) a := by
    rw [List.append_nil] at ha
    exact appendLeft_exec ha (![out,[],[],[]] : Fin 4 → List BSym)
  obtain ⟨b, hb, hbb⟩ := hw n out
  have hb' : (onPorts numeralWriterPorts writer).Exec (literalState s v g i unary out)
      (literalState s v g i unary tail) b := by
    apply onPorts_exec numeralWriterPorts hb
    · intro k
      fin_cases k <;> rfl
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      fin_cases k <;> first | rfl | exact (hk 1 rfl).elim
  have hc : (clearProg (6 : Fin 20)).Exec (literalState s v g i unary tail)
      (literalStore s v g i tail) (3*n+1) := by
    convert clear_exec (6 : Fin 20) (literalState s v g i unary tail) using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl) |
      (change 3*n+1 = 3*(List.replicate n BSym.one).length+1; simp)
  have hd : (pushProg (16 : Fin 20) (signBit positive)).Exec (literalStore s v g i tail)
      (literalStore s v g i (signBit positive :: tail)) 1 := by
    unfold pushProg
    convert StackProg.Exec.act _ (literalStore s v g i tail) using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  refine ⟨_, ha'.seq (hb'.seq (hc.seq hd)), ?_⟩
  change _ ≤ variableNameBound s v g i + C*(n+1)^2 + 3*n+5
  omega

def namedLiteralBound (C cap : ℕ) : ℕ :=
  let nameCap := variableNameCap cap
  let numeralCap := (nameCap+1)^2
  3*pairPassBound nameCap + 6*nameCap + C*(numeralCap+1)^2 + 3*numeralCap + 11

theorem namedLiteralBound_le (C s v g i cap : ℕ) (h : s+v+g+i ≤ cap) :
    variableNameBound s v g i + C*(literalIndex s v g i+1)^2 + 3*literalIndex s v g i+5 ≤
      namedLiteralBound C cap := by
  have hname := variableNameBound_le s v g i cap h
  have hnum := literalIndex_le s v g i cap h
  have hwrite : C*(literalIndex s v g i+1)^2 ≤ C*((variableNameCap cap+1)^2+1)^2 := by gcongr
  dsimp only [namedLiteralBound]
  omega

end FourToOneGames.SATMachine

end

/- SATLiteralCalls -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity WordMachines WordMachines.BankCalls
open WordMachines.LiftInput (appendLeft_exec)

structure LiteralSource (m : ℕ) where
  registers : Fin 4 → Fin m
  positive : Bool

variable {m : ℕ}

private def LiteralSource.inputs (l : LiteralSource m) : List (Fin m × Fin 20) :=
  [(l.registers 0,0), (l.registers 1,1), (l.registers 2,2), (l.registers 3,3)]

def LiteralSource.word (l : LiteralSource m) (p : Fin m → List BSym) : List BSym :=
  namedLiteralWord (p (l.registers 0)).length (p (l.registers 1)).length
    (p (l.registers 2)).length (p (l.registers 3)).length l.positive

def LiteralSource.ready (l : LiteralSource m) (p : Fin m → List BSym)
    (scratch out : Fin m) (cap : ℕ) : Prop :=
  ∀ j, p (l.registers j) = List.replicate (p (l.registers j)).length .one ∧
    (p (l.registers j)).length ≤ cap ∧ l.registers j ≠ scratch ∧ l.registers j ≠ out

theorem LiteralSource.ready_update {l : LiteralSource m} {p : Fin m → List BSym}
    {scratch out : Fin m} {cap : ℕ} (h : l.ready p scratch out cap) (tail : List BSym) :
    l.ready (Function.update p out tail) scratch out cap := by
  intro j
  simpa only [Function.update_of_ne (h j).2.2.2] using h j

theorem LiteralSource.word_update {l : LiteralSource m} {p : Fin m → List BSym}
    {scratch out : Fin m} {cap : ℕ} (h : l.ready p scratch out cap) (tail : List BSym) :
    l.word (Function.update p out tail) = l.word p := by
  unfold LiteralSource.word
  simp only [Function.update_of_ne (h _).2.2.2]

def literalCallBound (C cap : ℕ) : ℕ :=
  10*(4*(6*cap+4)+1) + 10*namedLiteralBound C (4*cap) + 7

/-- Run the named-literal writer on four read-only caller registers. -/
noncomputable def literalCall (writer : StackProg (Fin 5) BSym)
    (scratch out : Fin m) (literal : LiteralSource m) : StackProg (Fin (m+20)) BSym :=
  callBank scratch out 16 literal.inputs (namedLiteral writer literal.positive)

set_option maxHeartbeats 1500000 in
theorem literalCall_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (p : Fin m → List BSym) (scratch out : Fin m)
    (literal : LiteralSource m) (hready : literal.ready p scratch out cap)
    (hscratch : p scratch = []) (hosep : out ≠ scratch) :
    ∃ t, (literalCall writer scratch out literal).Exec
      (Fin.append p (fun _ : Fin 20 => []))
      (Fin.append (Function.update p out (literal.word p ++ p out)) (fun _ : Fin 20 => [])) t ∧
      t ≤ literalCallBound C cap := by
  let n (j : Fin 4) := (p (literal.registers j)).length
  let a := n 0
  let b := n 1
  let c := n 2
  let d := n 3
  have hstart : copiedInputs p literal.inputs (fun _ => []) = literalStore a b c d [] := by
    refine funext (fun k => ?_)
    fin_cases k <;> simp [LiteralSource.inputs, copiedInputs] <;>
      first
      | rfl
      | exact (hready 0).1
      | exact (hready 1).1
      | exact (hready 2).1
      | exact (hready 3).1
  obtain ⟨u, hu, hub⟩ := namedLiteral_exec writer C hw a b c d literal.positive []
  let word := literal.word p
  have hu' : (namedLiteral writer literal.positive).Exec
      (copiedInputs p literal.inputs (fun _ => [])) (literalStore a b c d word) u := by
    rw [hstart]
    simp only [List.append_nil] at hu
    exact hu
  have ha := (hready 0).2.1
  have hb := (hready 1).2.1
  have hc := (hready 2).2.1
  have hd := (hready 3).2.1
  have hnum : a+b+c+d ≤ 4*cap := by dsimp [a,b,c,d,n]; omega
  have huBound : u ≤ namedLiteralBound C (4*cap) :=
    hub.trans (namedLiteralBound_le C a b c d _ hnum)
  have hst : ∀ sd ∈ literal.inputs, sd.1 ≠ scratch := by
    intro sd hsd
    simp [LiteralSource.inputs] at hsd
    rcases hsd with rfl | rfl | rfl | rfl
    exacts [(hready 0).2.2.1, (hready 1).2.2.1, (hready 2).2.2.1, (hready 3).2.2.1]
  obtain ⟨t, ht, htb⟩ := callBank_exec p scratch out 16 literal.inputs
    (namedLiteral writer literal.positive) (literalStore a b c d word) word
    u (namedLiteralBound C (4*cap)) hscratch hosep hst hu' rfl huBound
  refine ⟨t, ht, htb.trans ?_⟩
  have hcopy : copyCost p literal.inputs ≤ 4*(6*cap+4)+1 := by
    simp only [LiteralSource.inputs, copyCost]
    omega
  unfold literalCallBound
  omega

end FourToOneGames.SATMachine

end

/- SATClauseMachine -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity WordMachines
open WordMachines.LiftInput (appendLeft_exec)

variable {m : ℕ}

theorem pushSymbol_exec {K A : Type} [DecidableEq K] (dst : K) (symbol : A) (p : K → List A) :
    (pushProg dst symbol).Exec p (Function.update p dst (symbol :: p dst)) 1 := by
  unfold pushProg
  convert StackProg.Exec.act _ p using 1
  exact funext (fun k => by by_cases hk : k = dst <;>
    simp [StackProg.applyAct, StackAct.apply, hk])

def literalWords (p : Fin m → List BSym) (literals : List (LiteralSource m)) : List BSym :=
  literals.flatMap (fun l => l.word p)

private noncomputable def emitLiterals (writer : StackProg (Fin 5) BSym)
    (scratch out : Fin m) : List (LiteralSource m) → StackProg (Fin (m+20)) BSym
  | [] => .act (fun _ _ => .keep)
  | l::ls => .seq (emitLiterals writer scratch out ls) (literalCall writer scratch out l)

private theorem emitLiterals_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (scratch out : Fin m) (hosep : out ≠ scratch)
    (ls : List (LiteralSource m)) (p : Fin m → List BSym) (hs : p scratch = [])
    (hr : ∀ l ∈ ls, l.ready p scratch out cap) :
    ∃ t, (emitLiterals writer scratch out ls).Exec
      (Fin.append p (fun _ : Fin 20 => []))
      (Fin.append (Function.update p out (literalWords p ls ++ p out))
        (fun _ : Fin 20 => [])) t ∧
      t ≤ ls.length*(literalCallBound C cap+1)+1 := by
  induction ls with
  | nil =>
      refine ⟨1, ?_, by simp⟩
      convert StackProg.Exec.act (fun _ _ => .keep) (Fin.append p (fun _ : Fin 20 => []))
        using 1 <;>
        (try simp [literalWords]) <;> rfl
  | cons l ls ih =>
      obtain ⟨u, hu, hub⟩ := ih (fun x hx => hr x (List.mem_cons_of_mem _ hx))
      let tail := literalWords p ls ++ p out
      let next := Function.update p out tail
      have hn : next scratch = [] := by simpa only [next, Function.update_of_ne hosep.symm] using hs
      have hready := hr l List.mem_cons_self
      obtain ⟨v, hv, hvb⟩ := literalCall_exec writer C cap hw next scratch out l
        (LiteralSource.ready_update hready tail) hn hosep
      have hfinal : Function.update next out (l.word next ++ next out) =
          Function.update p out (literalWords p (l::ls) ++ p out) := by
        rw [show l.word next = l.word p from LiteralSource.word_update hready tail]
        simp [next, tail, literalWords, List.append_assoc, Function.update_idem]
      rw [hfinal] at hv
      refine ⟨_, hu.seq hv, ?_⟩
      simp only [List.length_cons, Nat.succ_mul]
      omega

def nativeClauseWord (p : Fin m → List BSym) (literals : List (LiteralSource m)) : List BSym :=
  .minus :: literalWords p literals

/-- Read the literal operands from the caller and prepend the clause marker and the literals. -/
noncomputable def emitClause (writer : StackProg (Fin 5) BSym) (scratch out : Fin m)
    (literals : List (LiteralSource m)) : StackProg (Fin (m+20)) BSym :=
  .seq (emitLiterals writer scratch out literals)
    (onPorts (Fin.castAddEmb 20) (pushProg out .minus))

theorem emitClause_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (p : Fin m → List BSym) (scratch out : Fin m)
    (literals : List (LiteralSource m)) (hscratch : p scratch = []) (hosep : out ≠ scratch)
    (hready : ∀ l ∈ literals, l.ready p scratch out cap) :
    ∃ t, (emitClause writer scratch out literals).Exec (Fin.append p (fun _ : Fin 20 => []))
      (Fin.append (Function.update p out (nativeClauseWord p literals ++ p out))
        (fun _ : Fin 20 => [])) t ∧
      t ≤ literals.length*(literalCallBound C cap+1)+3 := by
  obtain ⟨u, hu, hub⟩ := emitLiterals_exec writer C cap hw scratch out hosep
    literals p hscratch hready
  let next := Function.update p out (literalWords p literals ++ p out)
  have hpush := pushSymbol_exec out BSym.minus next
  have hfinal : Function.update next out (.minus :: next out) =
      Function.update p out (nativeClauseWord p literals ++ p out) := by
    simp [next, nativeClauseWord, Function.update_idem]
  rw [hfinal] at hpush
  exact ⟨_, hu.seq (appendLeft_exec hpush (fun _ : Fin 20 => [])), by omega⟩

end FourToOneGames.SATMachine

end

/- SATChoiceMachine -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity WordMachines
open WordMachines.LiftInput (appendLeft_exec)

private def choiceParent (side vertex width i : ℕ) (succTape out : List BSym) :
    Fin 9 → List BSym :=
  ![List.replicate side .one, List.replicate vertex .one, List.replicate width .one,
    List.replicate i .one, succTape, [], [.one], out, []]

def choiceStore (side vertex width i : ℕ) (out : List BSym) : Fin 29 → List BSym :=
  Fin.append (choiceParent side vertex width i [] out) (fun _ : Fin 20 => [])

private def choiceGate (index : Fin 9) (positive : Bool) : LiteralSource 9 :=
  ⟨![0,1,6,index], positive⟩

private def choiceTransitionLiterals : List (LiteralSource 9) :=
  [choiceGate 4 false, choiceGate 3 true, ⟨![0,1,5,3], true⟩]

def choiceTransitionWord (side vertex i : ℕ) : List BSym :=
  .minus :: (namedLiteralWord side vertex 1 (i+1) false ++
    namedLiteralWord side vertex 1 i true ++ namedLiteralWord side vertex 0 i true)

private def prepareSuccessor : StackProg (Fin 9) BSym :=
  .seq (copyProg 3 4 8) (pushProg 4 .one)

noncomputable def choiceTransition (writer : StackProg (Fin 5) BSym) : StackProg (Fin 29) BSym :=
  .seq (onPorts (Fin.castAddEmb 20) prepareSuccessor)
    (.seq (emitClause writer 8 7 choiceTransitionLiterals)
      (onPorts (Fin.castAddEmb 20) (clearProg 4)))

def choiceTransitionBound (C cap : ℕ) : ℕ := 3*(literalCallBound C cap+1)+10*cap+24

private theorem prepareSuccessor_exec (s v d i : ℕ) (out : List BSym) :
    prepareSuccessor.Exec (choiceParent s v d i [] out)
      (choiceParent s v d i (List.replicate (i+1) .one) out) (6*i+5) := by
  let p := choiceParent s v d i [] out
  let q := choiceParent s v d i (List.replicate i .one) out
  have ha := stack_copy (3 : Fin 9) 4 8 (by decide) (by decide) (by decide) p rfl
  have hq : Function.update p 4 (p 3 ++ p 4) = q := by
    exact funext (fun k => by fin_cases k <;> simp [p, q, choiceParent])
  rw [hq] at ha
  have hb := pushSymbol_exec 4 BSym.one q
  have he : Function.update q 4 (.one :: q 4) =
      choiceParent s v d i (List.replicate (i+1) .one) out := by
    exact funext (fun k => by fin_cases k <;> rfl)
  rw [he] at hb
  have hn : (p 3).length = i := by change (List.replicate i BSym.one).length = i; simp
  rw [hn] at ha
  unfold prepareSuccessor
  exact ha.seq hb

private theorem transitionReady (s v d i cap : ℕ) (out : List BSym)
    (hs : s ≤ cap) (hv : v ≤ cap) (hi : i+1 ≤ cap) :
    ∀ lit ∈ choiceTransitionLiterals,
      lit.ready (choiceParent s v d i (List.replicate (i+1) .one) out) 8 7 cap := by
  intro lit hl
  simp [choiceTransitionLiterals] at hl
  rcases hl with rfl | rfl | rfl <;>
    intro j <;> fin_cases j <;>
    simp [choiceGate, choiceParent, hi, hs, hv, show i ≤ cap by omega, show 1 ≤ cap by omega]

private theorem transitionWord_eq (s v d i : ℕ) (out : List BSym) :
    nativeClauseWord (choiceParent s v d i (List.replicate (i+1) .one) out)
      choiceTransitionLiterals = choiceTransitionWord s v i := by
  simp [nativeClauseWord, literalWords, choiceTransitionLiterals, choiceTransitionWord,
    LiteralSource.word, choiceGate, choiceParent, List.append_assoc]

set_option maxHeartbeats 2000000 in
theorem choiceTransition_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (s v d i : ℕ) (out : List BSym)
    (hs : s ≤ cap) (hv : v ≤ cap) (hi : i+1 ≤ cap) :
    ∃ t, (choiceTransition writer).Exec (choiceStore s v d i out)
      (choiceStore s v d i (choiceTransitionWord s v i ++ out)) t ∧
      t ≤ choiceTransitionBound C cap := by
  let next := List.replicate (i+1) BSym.one
  let parent := choiceParent s v d i next out
  let w := choiceTransitionWord s v i ++ out
  have hprep := appendLeft_exec (prepareSuccessor_exec s v d i out) (fun _ : Fin 20 => [])
  obtain ⟨u, hu, hub⟩ := emitClause_exec writer C cap hw parent 8 7 choiceTransitionLiterals
    rfl (by decide) (transitionReady s v d i cap out hs hv hi)
  have he : Function.update parent 7 (nativeClauseWord parent choiceTransitionLiterals ++ parent 7) =
      choiceParent s v d i next w := by
    rw [show nativeClauseWord parent choiceTransitionLiterals = choiceTransitionWord s v i from
      transitionWord_eq s v d i out]
    exact funext (fun k => by fin_cases k <;> rfl)
  rw [he] at hu
  have hc : (clearProg (4 : Fin 9)).Exec (choiceParent s v d i next w)
      (choiceParent s v d i [] w) (3*(i+1)+1) := by
    convert clear_exec (4 : Fin 9) (choiceParent s v d i next w) using 1 <;>
      first
      | rfl
      | exact funext (fun k => by fin_cases k <;> rfl)
      | (change 3*(i+1)+1 = 3*(List.replicate (i+1) BSym.one).length+1; simp)
  refine ⟨_, hprep.seq (hu.seq (appendLeft_exec hc (fun _ : Fin 20 => []))), ?_⟩
  change _ ≤ 3*(literalCallBound C cap+1)+10*cap+24
  change u ≤ 3*(literalCallBound C cap+1)+3 at hub
  omega

private def unitLiterals (last : Bool) : List (LiteralSource 9) :=
  List.replicate 3 (choiceGate (if last then 2 else 5) last)

def choiceUnitWord (s v i : ℕ) (positive : Bool) : List BSym :=
  let lit := namedLiteralWord s v 1 i positive
  .minus :: (lit ++ lit ++ lit)

noncomputable def choiceUnit (writer : StackProg (Fin 5) BSym) (last : Bool) :
    StackProg (Fin 29) BSym := emitClause writer 8 7 (unitLiterals last)

def choiceUnitBound (C cap : ℕ) : ℕ := 3*(literalCallBound C cap+1)+3

theorem choiceUnit_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (s v d i : ℕ) (last : Bool) (out : List BSym)
    (hs : s ≤ cap) (hv : v ≤ cap) (hd : d ≤ cap) (hcap : 1 ≤ cap) :
    ∃ t, (choiceUnit writer last).Exec (choiceStore s v d i out)
      (choiceStore s v d i (choiceUnitWord s v (if last then d else 0) last ++ out)) t ∧
      t ≤ choiceUnitBound C cap := by
  let parent := choiceParent s v d i [] out
  have hready : ∀ lit ∈ unitLiterals last, lit.ready parent 8 7 cap := by
    intro lit hmem
    have h := List.eq_of_mem_replicate hmem
    subst lit
    intro j
    cases last <;> fin_cases j <;>
      simp [choiceGate, parent, choiceParent, hs, hv, hd, hcap]
  obtain ⟨t, ht, htb⟩ := emitClause_exec writer C cap hw parent 8 7 (unitLiterals last)
    rfl (by decide) hready
  have hword : nativeClauseWord parent (unitLiterals last) =
      choiceUnitWord s v (if last then d else 0) last := by
    cases last <;>
      simp [parent, choiceParent, nativeClauseWord, literalWords, unitLiterals, choiceGate,
        choiceUnitWord, LiteralSource.word, List.replicate_succ, List.append_assoc]
  rw [hword] at ht
  have hfinal : Function.update parent 7
      (choiceUnitWord s v (if last then d else 0) last ++ parent 7) =
      choiceParent s v d i [] (choiceUnitWord s v (if last then d else 0) last ++ out) :=
    funext (fun k => by fin_cases k <;> rfl)
  rw [hfinal] at ht
  exact ⟨t, ht, by simpa [choiceUnitBound, unitLiterals] using htb⟩

private theorem choiceLabelFrame (s v d i : ℕ) (out : List BSym) :
    countFrame (choiceStore s v d 0 []) 3 7 .one i out = choiceStore s v d i out := by
  unfold countFrame choiceStore
  rw [show (3 : Fin 29) = (3 : Fin 9).castAdd 20 from rfl,
    show (7 : Fin 29) = (7 : Fin 9).castAdd 20 from rfl,
    BankCalls.append_update_left, BankCalls.append_update_left]
  congr 1
  exact funext (fun k => by fin_cases k <;> rfl)

def vertexChoiceWord (s v d : ℕ) : List BSym :=
  choiceUnitWord s v 0 false ++ choiceUnitWord s v d true ++
    ascendingWords (choiceTransitionWord s v) d

/-- Emit the two unit clauses and all the label-choice clauses for one vertex. -/
noncomputable def vertexChoices (writer : StackProg (Fin 5) BSym) : StackProg (Fin 29) BSym :=
  .seq (onPorts (Fin.castAddEmb 20) (copyProg 2 3 8))
    (.seq (emitCounted 3 (choiceTransition writer))
      (.seq (choiceUnit writer true) (choiceUnit writer false)))

def vertexChoicesBound (C cap : ℕ) : ℕ :=
  cap*(choiceTransitionBound C cap+4)+6*cap+2*choiceUnitBound C cap+7

theorem vertexChoices_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (s v d : ℕ) (out : List BSym)
    (hs : s ≤ cap) (hv : v ≤ cap) (hd : d ≤ cap) (hcap : 1 ≤ cap) :
    ∃ t, (vertexChoices writer).Exec (choiceStore s v d 0 out)
      (choiceStore s v d 0 (vertexChoiceWord s v d ++ out)) t ∧
      t ≤ vertexChoicesBound C cap := by
  let parent := choiceParent s v d 0 [] out
  have hp := stack_copy (2 : Fin 9) 3 8 (by decide) (by decide) (by decide) parent rfl
  have hnew : Function.update parent 3 (parent 2 ++ parent 3) =
      choiceParent s v d d [] out := funext (fun k => by fin_cases k <;> simp [parent, choiceParent])
  have hlen : (parent 2).length = d := by change (List.replicate d BSym.one).length = d; simp
  rw [hnew, hlen] at hp
  obtain ⟨a, ha, hab⟩ := emitCounted_exec (choiceStore s v d 0 []) 3 7 (by decide)
    .one (choiceTransition writer) (choiceTransitionWord s v) d (choiceTransitionBound C cap)
    (fun j hj tail => by
      simp only [choiceLabelFrame]
      exact choiceTransition_exec writer C cap hw s v d j tail hs hv (by omega)) out
  rw [choiceLabelFrame, choiceLabelFrame] at ha
  let tail := ascendingWords (choiceTransitionWord s v) d ++ out
  obtain ⟨b, hb, hbb⟩ := choiceUnit_exec writer C cap hw s v d 0 true tail hs hv hd hcap
  obtain ⟨c, hc, hcb⟩ := choiceUnit_exec writer C cap hw s v d 0 false
    (choiceUnitWord s v d true ++ tail) hs hv hd hcap
  have he := (appendLeft_exec hp (fun _ : Fin 20 => [])).seq (ha.seq (hb.seq hc))
  refine ⟨6*d+3+1+(a+1+(b+1+c)), ?_, ?_⟩
  · simpa [vertexChoiceWord, tail, List.append_assoc, vertexChoices, choiceStore, parent] using he
  · have hmul : d*(choiceTransitionBound C cap+4) ≤ cap*(choiceTransitionBound C cap+4) :=
      Nat.mul_le_mul_right _ hd
    unfold vertexChoicesBound
    omega

private theorem choiceVertexFrame (s v d : ℕ) (out : List BSym) :
    countFrame (choiceStore s 0 d 0 []) 1 7 .one v out = choiceStore s v d 0 out := by
  unfold countFrame choiceStore
  rw [show (1 : Fin 29) = (1 : Fin 9).castAdd 20 from rfl,
    show (7 : Fin 29) = (7 : Fin 9).castAdd 20 from rfl,
    BankCalls.append_update_left, BankCalls.append_update_left]
  congr 1
  exact funext (fun k => by fin_cases k <;> rfl)

def vertexSideWord (side count width : ℕ) : List BSym :=
  ascendingWords (fun v => vertexChoiceWord side v width) count

noncomputable def vertexSide (writer : StackProg (Fin 5) BSym) : StackProg (Fin 29) BSym :=
  emitCounted 1 (vertexChoices writer)

def vertexSideBound (C cap : ℕ) : ℕ := cap*(vertexChoicesBound C cap+4)+1

theorem vertexSide_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (side count width : ℕ) (tail : List BSym)
    (hs : side ≤ cap) (hn : count ≤ cap) (hd : width ≤ cap) (hcap : 1 ≤ cap) :
    ∃ t, (vertexSide writer).Exec (choiceStore side count width 0 tail)
      (choiceStore side 0 width 0 (vertexSideWord side count width ++ tail)) t ∧
      t ≤ vertexSideBound C cap := by
  obtain ⟨t, ht, hb⟩ := emitCounted_exec (choiceStore side 0 width 0 []) 1 7 (by decide)
    .one (vertexChoices writer) (fun v => vertexChoiceWord side v width)
    count (vertexChoicesBound C cap)
    (fun v hv out => by
      simp only [choiceVertexFrame]
      exact vertexChoices_exec writer C cap hw side v width out hs (hv.le.trans hn) hd hcap) tail
  exact ⟨t, by simpa only [choiceVertexFrame, vertexSide, vertexSideWord] using ht,
    hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)⟩

end FourToOneGames.SATMachine

end

/- SATFormulaLayout -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open OAI.PerfectCompleteness.BinaryFormula
open WordMachines

private def gateUnitClause (s v i : ℕ) (sign : Bool) : Clause :=
  let l : Literal := ⟨literalIndex s v 1 i, sign⟩
  #v[l,l,l]

private def transitionClause (s v i : ℕ) : Clause :=
  #v[⟨literalIndex s v 1 (i+1), false⟩,
    ⟨literalIndex s v 1 i, true⟩, ⟨literalIndex s v 0 i, true⟩]

private theorem gateUnitClause_word (s v i : ℕ) (sign : Bool) :
    clauseWord (gateUnitClause s v i sign) = choiceUnitWord s v i sign := rfl

private theorem transitionClause_word (s v i : ℕ) :
    clauseWord (transitionClause s v i) = choiceTransitionWord s v i := rfl

/-- The checked vertex macro emits the exact clause words of the SAT construction. -/
theorem vertexChoiceWord_spec (s v d : ℕ) :
    (choiceClauses d (literalIndex s v 0) (literalIndex s v 1)).flatMap clauseWord =
      vertexChoiceWord s v d := by
  change ((gateUnitClause s v 0 false) :: (gateUnitClause s v d true) ::
      (List.range d).map (transitionClause s v)).flatMap clauseWord = _
  simp only [vertexChoiceWord, ascendingWords, List.flatMap_cons, List.flatMap_map,
    gateUnitClause_word, transitionClause_word, List.append_assoc]

theorem vertexSideWord_spec (s n d : ℕ) :
    ((List.range n).flatMap fun v => choiceClauses d
      (literalIndex s v 0) (literalIndex s v 1)).flatMap clauseWord = vertexSideWord s n d := by
  simp only [vertexSideWord, ascendingWords, List.flatMap_assoc, vertexChoiceWord_spec]

def conflictClause (u v a b : ℕ) : Clause :=
  let left : Literal := ⟨literalIndex 0 u 0 a, false⟩
  let right : Literal := ⟨literalIndex 1 v 0 b, false⟩
  #v[left,right,right]

def constantUnitClause (positive : Bool) : Clause :=
  let l : Literal := ⟨0,positive⟩
  #v[l,l,l]

/-- Unfold the existing formula at its vertex and constraint boundaries. -/
theorem satFormula_layout (P : LabelCover) :
    (satFormula P).clauses =
      if P.edges.Nonempty then
        ((List.range P.nL).flatMap fun u =>
          choiceClauses P.sizeL (literalIndex 0 u 0) (literalIndex 0 u 1)) ++
        ((List.range P.nR).flatMap fun v =>
          choiceClauses P.sizeR (literalIndex 1 v 0) (literalIndex 1 v 1)) ++
        ((List.finRange P.nL).flatMap fun u =>
          (List.finRange P.nR).flatMap fun v =>
            if (u,v) ∈ P.edges then
              (List.finRange P.sizeL).flatMap fun a =>
                ((List.finRange P.sizeR).filter fun b => decide (P.proj u v a ≠ b)).map
                  (fun b => conflictClause u.val v.val a.val b.val)
            else [])
      else [constantUnitClause true, constantUnitClause false] := rfl

end FourToOneGames.SATMachine

end

/- SATTableReads -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity WordMachines WordMachines.BankCalls
open WordMachines.LiftInput (appendLeft_exec)

private def peekSymbol {A : Type} : StackProg (Fin 6) A :=
  .act (fun h k => if k = 2 then (h 0).elim .keep .push else .keep)

/-- Skip an indexed prefix and return the next symbol on the work bank's output tape. -/
def readSymbol {A : Type} : StackProg (Fin 6) A :=
  .seq splitPrefix (.seq (clearProg 2) peekSymbol)

set_option maxHeartbeats 1000000 in
theorem readSymbol_exec {A : Type} (pre suffix index : List A) (symbol : A)
    (hindex : index.length = pre.length) :
    readSymbol.Exec (lookupStore (pre ++ symbol :: suffix) index [])
      (lookupStore (symbol :: suffix) index [symbol]) (15*pre.length+11) := by
  let mid := lookupStore (symbol :: suffix) index []
  have hskip := splitPrefix_exec pre (symbol :: suffix) index [] hindex
  rw [List.append_nil] at hskip
  have hclear : (clearProg (2 : Fin 6)).Exec (lookupStore (symbol :: suffix) index pre)
      mid (3*pre.length+1) := by
    convert clear_exec (2 : Fin 6) (lookupStore (symbol :: suffix) index pre) using 1 <;>
      first | rfl | exact funext (fun k => by fin_cases k <;> rfl)
  have hpeek : peekSymbol.Exec mid (lookupStore (symbol :: suffix) index [symbol]) 1 := by
    unfold peekSymbol
    convert StackProg.Exec.act _ mid using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  convert hskip.seq (hclear.seq hpeek) using 1 <;> first | rfl | omega

def nativeAdjacency (P : LabelCover) : List BSym := (adjacencyBits P).map nativeBit
def nativeProjection (P : LabelCover) : List BSym := (projectionPayload P).map nativeBit

private theorem denseIndex_lt {u rows v cols : ℕ} (hu : u < rows) (hv : v < cols) :
    u*cols + v < rows*cols := by
  have step := Nat.mul_le_mul_right cols (Nat.succ_le_of_lt hu)
  rw [Nat.succ_mul] at step
  omega

theorem nativeAdjacency_length (P : LabelCover) : (nativeAdjacency P).length = P.nL * P.nR := by
  simp [nativeAdjacency, adjacencyBits_length]

theorem nativeAdjacency_read (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR) :
    let i := u.val*P.nR + v.val
    let index := List.replicate i BSym.one
    let flag := nativeBit (decide ((u,v) ∈ P.edges))
    readSymbol.Exec (lookupStore (nativeAdjacency P) index [])
      (lookupStore (flag :: (nativeAdjacency P).drop (i+1)) index [flag]) (15*i+11) := by
  dsimp only
  let w := nativeAdjacency P
  let i := u.val*P.nR + v.val
  have hi : i < w.length := by
    rw [nativeAdjacency_length]
    exact denseIndex_lt u.isLt v.isLt
  have hflag : w[i] = nativeBit (decide ((u,v) ∈ P.edges)) := by
    simpa [w, nativeAdjacency] using congrArg nativeBit (adjacencyBits_get P u v)
  have hsplit : w = w.take i ++ nativeBit (decide ((u,v) ∈ P.edges)) :: w.drop (i+1) := by
    nth_rw 1 [← List.take_append_drop i w]
    rw [List.drop_eq_getElem_cons hi, hflag]
  have hlength : (w.take i).length = i := by simp [Nat.min_eq_left hi.le]
  have hr := readSymbol_exec (w.take i) (w.drop (i+1)) (List.replicate i BSym.one)
    (nativeBit (decide ((u,v) ∈ P.edges))) (by simp [hlength])
  rw [← hsplit, hlength] at hr
  exact hr

theorem nativeProjection_layout (P : LabelCover) :
    nativeProjection P = (projectionWords P).flatMap (unary BSym.one BSym.zero) := by
  simp [nativeProjection, projectionPayload, unary, List.map_flatMap, nativeBit]
  rfl

/-- Read the dense projection field indexed by the two vertices and a left label. -/
theorem nativeProjection_read (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR)
    (a : Fin P.sizeL) (out : List BSym) :
    let i := (u.val*P.nR + v.val)*P.sizeL + a.val
    let index := List.replicate i BSym.one
    ∃ t, (lookupField .one).Exec (lookupStore (nativeProjection P) index out)
      (lookupStore (nativeProjection P) index (List.replicate (P.proj u v a).val .one ++ out)) t ∧
      t ≤ 10*(nativeProjection P).length + 10*i + 15 := by
  dsimp only
  let i := (u.val*P.nR + v.val)*P.sizeL + a.val
  have hix : i = u.val*(P.nR*P.sizeL) + (v.val*P.sizeL+a.val) := by
    simp [i, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  have hvalid : i < (projectionWords P).length := by
    rw [hix, projectionWords_length]
    exact denseIndex_lt u.isLt (denseIndex_lt v.isLt a.isLt)
  obtain ⟨t, ht, hb⟩ := lookupField_at BSym.one BSym.zero (projectionWords P)
    (List.replicate i BSym.one) out (by decide) (by simpa only [List.length_replicate] using hvalid)
  have hp : (projectionWords P)[i] = (P.proj u v a).val := by
    simpa only [hix] using projectionWords_get P u v a
  exact ⟨t, by simpa only [List.length_replicate, hp, ← nativeProjection_layout P] using ht,
    by simpa only [List.length_replicate, ← nativeProjection_layout P] using hb⟩

private def queryInputs {m : ℕ} (src index : Fin m) : List (Fin m × Fin 20) :=
  [(src,0),(index,1)]

/-- Read a copied table and return the requested field to the caller. -/
noncomputable def queryTable {m : ℕ} (src index scratch out : Fin m)
    (reader : StackProg (Fin 6) BSym) : StackProg (Fin (m+20)) BSym :=
  callBank scratch out 2 (queryInputs src index) (onPorts (Fin.castAddEmb 14) reader)

def queryTableBound (wordLen indexLen budget : ℕ) : ℕ :=
  10*(6*(wordLen+indexLen)+9)+10*budget+7

set_option maxHeartbeats 1500000 in
theorem queryTable_exec {m : ℕ} (p : Fin m → List BSym) (src index scratch out : Fin m)
    (reader : StackProg (Fin 6) BSym) (finish : Fin 6 → List BSym) (word : List BSym)
    (t budget : ℕ) (hscratch : p scratch = []) (hs : src ≠ scratch) (hi : index ≠ scratch)
    (ho : out ≠ scratch) (hr : reader.Exec (lookupStore (p src) (p index) []) finish t)
    (hword : finish 2 = word) (hbudget : t ≤ budget) :
    ∃ u, (queryTable src index scratch out reader).Exec (Fin.append p (fun _ : Fin 20 => []))
      (Fin.append (Function.update p out (word ++ p out)) (fun _ : Fin 20 => [])) u ∧
      u ≤ queryTableBound (p src).length (p index).length budget := by
  let empty := fun _ : Fin 14 => ([] : List BSym)
  have hl := appendLeft_exec hr empty
  have hload : copiedInputs p (queryInputs src index) (fun _ => []) =
      Fin.append (lookupStore (p src) (p index) []) empty := by
    exact funext (fun k => by fin_cases k <;> simp [copiedInputs, queryInputs] <;> rfl)
  rw [← hload] at hl
  have hb : ∀ field ∈ queryInputs src index, field.1 ≠ scratch := by
    intro field hmem
    simp [queryInputs] at hmem
    rcases hmem with rfl | rfl <;> assumption
  obtain ⟨u, hu, hub⟩ := callBank_exec p scratch out 2 (queryInputs src index)
    (onPorts (Fin.castAddEmb 14) reader) (Fin.append finish empty) word t budget
    hscratch ho hb hl hword hbudget
  refine ⟨u, hu, hub.trans ?_⟩
  simp only [queryInputs, copyCost, queryTableBound]
  omega

theorem nativeAdjacency_address_lt (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR) :
    u.val*P.nR+v.val < (nativeAdjacency P).length := by
  rw [nativeAdjacency_length]
  exact denseIndex_lt u.isLt v.isLt

theorem nativeProjection_address_lt (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR)
    (a : Fin P.sizeL) : (u.val*P.nR+v.val)*P.sizeL+a.val < (nativeProjection P).length := by
  have hindex : (u.val*P.nR+v.val)*P.sizeL+a.val < (projectionWords P).length := by
    rw [projectionWords_length, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    exact denseIndex_lt u.isLt (denseIndex_lt v.isLt a.isLt)
  apply hindex.trans_le
  rw [nativeProjection_layout]
  generalize projectionWords P = widths
  induction widths with
  | nil => simp
  | cons n widths ih =>
    simp only [List.flatMap_cons, List.length_cons, List.length_append, unary,
      List.length_replicate]
    omega

end FourToOneGames.SATMachine

end

/- SATConflictMachine -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity WordMachines
open WordMachines.LiftInput (appendLeft_exec)

private noncomputable def nativeEquality : StackProg (Fin 6) BSym :=
  StackProgAlphabet.mapProg nativeBit fromNativeBit (UnaryComparison.compare false)

private def equalityStore (a b : ℕ) (flags : List BSym) : Fin 6 → List BSym :=
  ![List.replicate a .one, List.replicate b .one, [], [], [], flags]

private theorem nativeEquality_exec (a b : ℕ) :
    ∃ t, nativeEquality.Exec (equalityStore a b [])
      (equalityStore a b [nativeBit (decide (a=b))]) t ∧ t ≤ 12*(a+b)+15 := by
  obtain ⟨t, ht, hb⟩ := UnaryComparison.compare_exec false a b []
  have hinv : Function.LeftInverse fromNativeBit nativeBit := by
    intro x
    cases x <;> rfl
  have hs (flags : List Bool) : StackProgAlphabet.mapStore nativeBit
      (UnaryComparison.inputStore a b flags) = equalityStore a b (flags.map nativeBit) := by
    funext k
    fin_cases k <;>
      first
      | rfl
      | change (List.replicate _ true).map nativeBit = List.replicate _ BSym.one
        simp [nativeBit]
  have hr := StackProgAlphabet.mapProg_exec nativeBit fromNativeBit hinv ht
  rw [hs, hs] at hr
  exact ⟨t, hr, hb⟩

private theorem equalityOn_exec {K : Type} [DecidableEq K] (ports : Fin 6 ↪ K)
    (p : K → List BSym) (a b : ℕ)
    (ha : p (ports 0) = List.replicate a .one) (hb : p (ports 1) = List.replicate b .one)
    (h₂ : p (ports 2) = []) (h₃ : p (ports 3) = []) (h₄ : p (ports 4) = [])
    (h₅ : p (ports 5) = []) :
    ∃ t, (onPorts ports nativeEquality).Exec p
      (Function.update p (ports 5) [nativeBit (decide (a=b))]) t ∧ t ≤ 12*(a+b)+15 := by
  obtain ⟨t, ht, htb⟩ := nativeEquality_exec a b
  refine ⟨t, onPorts_exec ports ht ?_ ?_ ?_, htb⟩
  · intro k
    fin_cases k <;> simp [equalityStore, ha, hb, h₂, h₃, h₄, h₅]
  · intro k
    fin_cases k <;> simp [equalityStore, ha, hb, h₂, h₃, h₄, ports.injective.eq_iff]
  · intro k hk
    simp only [Function.update_of_ne (Ne.symm (hk 5))]

/-- The edge clause registers include both tables, their dimensions, and the four traversal indices. -/
def conflictParent (P : LabelCover) (u v a b row field expected : ℕ)
    (adjacent equal out : List BSym) : Fin 21 → List BSym :=
  ![nativeAdjacency P, nativeProjection P, List.replicate P.nR .one,
    List.replicate P.sizeL .one, List.replicate P.sizeR .one,
    List.replicate u .one, List.replicate v .one, List.replicate a .one,
    List.replicate row .one, List.replicate field .one, [], [], adjacent,
    List.replicate expected .one, List.replicate b .one,
    [.one], [], out, [], [], equal]

def conflictStore (P : LabelCover) (u v a b row field expected : ℕ)
    (adjacent out : List BSym) : Fin 41 → List BSym :=
  Fin.append (conflictParent P u v a b row field expected adjacent [] out)
    (fun _ : Fin 20 => [])

private def equalityPorts : Fin 6 ↪ Fin 21 := ⟨![13,14,10,11,19,20], by decide⟩

private def missesProjection (h : Fin 41 → Option BSym) : Bool :=
  h 20 == some BSym.zero

private def conflictLiterals : List (LiteralSource 21) :=
  let left : LiteralSource 21 := ⟨![16,5,16,7], false⟩
  let right : LiteralSource 21 := ⟨![15,6,16,14], false⟩
  [left,right,right]

private def idle : StackProg (Fin 41) BSym := .act (fun _ _ => .keep)

noncomputable def conflictTrial (writer : StackProg (Fin 5) BSym) : StackProg (Fin 41) BSym :=
  .seq (onPorts (Fin.castAddEmb 20) (onPorts equalityPorts nativeEquality))
    (.seq (.branch missesProjection (emitClause writer 18 17 conflictLiterals) idle)
      (onPorts (Fin.castAddEmb 20) (popProg 20)))

def conflictTrialWord (u v a b expected : ℕ) : List BSym :=
  if expected = b then [] else clauseWord (conflictClause u v a b)

def conflictTrialBound (C cap : ℕ) : ℕ := 3*(literalCallBound C cap+1)+24*cap+30

set_option maxHeartbeats 2500000 in
theorem conflictTrial_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (P : LabelCover) (u v a b row field expected : ℕ)
    (adjacent out : List BSym) (hu : u ≤ cap) (hv : v ≤ cap) (ha : a ≤ cap)
    (hb : b ≤ cap) (he : expected ≤ cap) (hcap : 1 ≤ cap) :
    ∃ t, (conflictTrial writer).Exec (conflictStore P u v a b row field expected adjacent out)
      (conflictStore P u v a b row field expected adjacent
        (conflictTrialWord u v a b expected ++ out)) t ∧
      t ≤ conflictTrialBound C cap := by
  let parent := conflictParent P u v a b row field expected adjacent
  let mark := [nativeBit (decide (expected=b))]
  let empty := fun _ : Fin 20 => ([] : List BSym)
  let w := conflictTrialWord u v a b expected ++ out
  obtain ⟨t, ht, htb⟩ := equalityOn_exec equalityPorts (parent [] out) expected b
    rfl rfl rfl rfl rfl rfl
  have hEq : Function.update (parent [] out) (equalityPorts 5) mark = parent mark out :=
    funext (fun k => by fin_cases k <;> rfl)
  change (onPorts equalityPorts nativeEquality).Exec _
    (Function.update (parent [] out) (equalityPorts 5) mark) _ at ht
  rw [hEq] at ht
  have hcompare := appendLeft_exec ht empty
  have hp : (popProg (20 : Fin 21)).Exec (parent mark w) (parent [] w) 1 := by
    convert pop_exec (20 : Fin 21) (parent mark w) using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have hpop := appendLeft_exec hp empty
  by_cases hmatch : expected = b
  · have hword : w = out := by simp [w, conflictTrialWord, hmatch]
    have hguard : missesProjection (fun k => (Fin.append (parent mark out) empty k).head?) =
        false := by
      change (some (nativeBit (decide (expected=b))) == some BSym.zero) = false
      simp [hmatch, nativeBit]
    have hidle : idle.Exec (Fin.append (parent mark out) empty) (Fin.append (parent mark w) empty) 1 := by
      rw [hword]
      unfold idle
      convert StackProg.Exec.act (fun _ _ => .keep) (Fin.append (parent mark out) empty) using 1
      exact funext (fun _ => rfl)
    refine ⟨_, hcompare.seq ((StackProg.Exec.branchFalse (p := emitClause writer 18 17 conflictLiterals)
      hguard hidle).seq hpop), ?_⟩
    unfold conflictTrialBound
    omega
  · have hguard : missesProjection (fun k => (Fin.append (parent mark out) empty k).head?) =
        true := by
      change (some (nativeBit (decide (expected=b))) == some BSym.zero) = true
      simp [hmatch, nativeBit]
    have hready : ∀ l ∈ conflictLiterals, l.ready (parent mark out) 18 17 cap := by
      intro lit hmem
      simp [conflictLiterals] at hmem
      rcases hmem with rfl | rfl <;> intro k <;> fin_cases k <;>
        simp [parent, conflictParent, hu, hv, ha, hb, hcap]
    obtain ⟨r, hr, hrb⟩ := emitClause_exec writer C cap hw (parent mark out) 18 17
      conflictLiterals rfl (by decide) hready
    have hwrd : nativeClauseWord (parent mark out) conflictLiterals =
        clauseWord (conflictClause u v a b) := by
      simp [nativeClauseWord, literalWords, conflictLiterals, LiteralSource.word,
        parent, conflictParent]
      rw [← List.append_assoc]
      rfl
    have hend : Function.update (parent mark out) 17
        (nativeClauseWord (parent mark out) conflictLiterals ++ parent mark out 17) = parent mark w := by
      rw [hwrd, show w = clauseWord (conflictClause u v a b) ++ out by
        simp [w, conflictTrialWord, hmatch]]
      exact funext (fun k => by fin_cases k <;> rfl)
    rw [hend] at hr
    refine ⟨_, hcompare.seq ((StackProg.Exec.branchTrue (q := idle) hguard hr).seq hpop), ?_⟩
    change r ≤ 3*(literalCallBound C cap+1)+3 at hrb
    unfold conflictTrialBound
    omega

private theorem conflictLabelFrame (P : LabelCover) (u v a row field expected b : ℕ)
    (adjacent out : List BSym) :
    countFrame (conflictStore P u v a 0 row field expected adjacent []) 14 17 .one b out =
      conflictStore P u v a b row field expected adjacent out := by
  unfold countFrame conflictStore
  rw [show (14 : Fin 41) = (14 : Fin 21).castAdd 20 from rfl,
    show (17 : Fin 41) = (17 : Fin 21).castAdd 20 from rfl,
    BankCalls.append_update_left, BankCalls.append_update_left]
  congr 1
  exact funext (fun k => by fin_cases k <;> rfl)

def conflictLabelsWord (u v a expected width : ℕ) : List BSym :=
  ascendingWords (fun b => conflictTrialWord u v a b expected) width

noncomputable def conflictLabels (writer : StackProg (Fin 5) BSym) : StackProg (Fin 41) BSym :=
  .seq (onPorts (Fin.castAddEmb 20) (copyProg 4 14 18))
    (emitCounted 14 (conflictTrial writer))

def conflictLabelsBound (C cap : ℕ) : ℕ := cap*(conflictTrialBound C cap+4)+6*cap+5

theorem conflictLabels_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (P : LabelCover) (u v a row field expected : ℕ)
    (adjacent out : List BSym) (hu : u ≤ cap) (hv : v ≤ cap) (ha : a ≤ cap)
    (hwidth : P.sizeR ≤ cap) (he : expected ≤ cap) (hcap : 1 ≤ cap) :
    ∃ t, (conflictLabels writer).Exec (conflictStore P u v a 0 row field expected adjacent out)
      (conflictStore P u v a 0 row field expected adjacent
        (conflictLabelsWord u v a expected P.sizeR ++ out)) t ∧ t ≤ conflictLabelsBound C cap := by
  let parent := conflictParent P u v a 0 row field expected adjacent [] out
  have hcopy := stack_copy (4 : Fin 21) 14 18 (by decide) (by decide) (by decide) parent rfl
  have hnew : Function.update parent 14 (parent 4 ++ parent 14) =
      conflictParent P u v a P.sizeR row field expected adjacent [] out :=
    funext (fun k => by fin_cases k <;> simp [parent, conflictParent])
  have hlength : (parent 4).length = P.sizeR := List.length_replicate
  rw [hnew, hlength] at hcopy
  obtain ⟨t, ht, htb⟩ := emitCounted_exec (conflictStore P u v a 0 row field expected adjacent [])
    14 17 (by decide) .one (conflictTrial writer) (fun b => conflictTrialWord u v a b expected)
    P.sizeR (conflictTrialBound C cap)
    (fun b hb tail => by
      simp only [conflictLabelFrame]
      exact conflictTrial_exec writer C cap hw P u v a b row field expected adjacent tail
        hu hv ha (hb.le.trans hwidth) he hcap) out
  have ht' := ht
  simp only [conflictLabelFrame] at ht'
  refine ⟨_, (appendLeft_exec hcopy (fun _ : Fin 20 => [])).seq ht', ?_⟩
  have hmul := Nat.mul_le_mul_right (conflictTrialBound C cap+4) hwidth
  unfold conflictLabelsBound
  omega

end FourToOneGames.SATMachine

end

/- SATDenseIndices -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open ProjSchedTW.Complexity CookPvsNP WordMachines

private def adjacencyAddressPorts : Fin 5 ↪ Fin 9 := ⟨![0,1,5,7,8], by decide⟩
private def projectionAddressPorts : Fin 5 ↪ Fin 9 := ⟨![5,3,6,7,8], by decide⟩

def denseIndexStore (u cols v width a rowIndex fieldIndex : ℕ) : Fin 9 → List BSym :=
  ![List.replicate u .one, List.replicate cols .one, List.replicate v .one,
    List.replicate width .one, List.replicate a .one, List.replicate rowIndex .one,
    List.replicate fieldIndex .one, [], []]

/-- Compute the adjacency and projection offsets in the published dense tables. -/
noncomputable def denseIndices : StackProg (Fin 9) BSym :=
  .seq (onPorts adjacencyAddressPorts multiply)
    (.seq (copyProg 2 5 8)
      (.seq (onPorts projectionAddressPorts multiply) (copyProg 4 6 8)))

def denseIndicesBound (cap : ℕ) : ℕ :=
  (6*cap+13)*cap + (6*(cap+1)^2+13)*cap + 12*cap + 30

set_option maxHeartbeats 1500000 in
theorem denseIndices_exec (u cols v width a cap : ℕ)
    (hu : u ≤ cap) (hc : cols ≤ cap) (hv : v ≤ cap) (hw : width ≤ cap) (ha : a ≤ cap) :
    let r := u*cols+v
    let i := r*width+a
    ∃ t, denseIndices.Exec (denseIndexStore u cols v width a 0 0)
      (denseIndexStore u cols v width a r i) t ∧ t ≤ denseIndicesBound cap := by
  dsimp only
  let product := u*cols
  let row := product+v
  let field := row*width
  let p := denseIndexStore u cols v width a
  have hm₀ : (onPorts adjacencyAddressPorts multiply).Exec (p 0 0) (p product 0)
      ((6*u+13)*cols+5) := by
    have hm := multiplyOn_exec adjacencyAddressPorts (p 0 0) BSym.one u cols rfl rfl rfl rfl
    convert hm using 1
    exact funext (fun k => by fin_cases k <;> simp [p, product, denseIndexStore, adjacencyAddressPorts])
  have hc₀ := stack_copy (2 : Fin 9) 5 8 (by decide) (by decide) (by decide) (p product 0) rfl
  have he₀ : Function.update (p product 0) 5 ((p product 0) 2 ++ (p product 0) 5) = p row 0 := by
    exact funext (fun k => by fin_cases k <;> simp [p, row, denseIndexStore, Nat.add_comm])
  have hl₀ : ((p product 0) 2).length = v := List.length_replicate
  rw [he₀, hl₀] at hc₀
  have hm₁ : (onPorts projectionAddressPorts multiply).Exec (p row 0) (p row field)
      ((6*row+13)*width+5) := by
    have hm := multiplyOn_exec projectionAddressPorts (p row 0) BSym.one row width rfl rfl rfl rfl
    convert hm using 1
    exact funext (fun k => by fin_cases k <;> simp [p, field, denseIndexStore, projectionAddressPorts])
  have hc₁ := stack_copy (4 : Fin 9) 6 8 (by decide) (by decide) (by decide) (p row field) rfl
  have he₁ : Function.update (p row field) 6 ((p row field) 4 ++ (p row field) 6) =
      p row (field+a) := by
    exact funext (fun k => by fin_cases k <;> simp [p, denseIndexStore, Nat.add_comm])
  have hl₁ : ((p row field) 4).length = a := List.length_replicate
  rw [he₁, hl₁] at hc₁
  have hprod : product ≤ cap*cap := Nat.mul_le_mul hu hc
  have hrow : row ≤ (cap+1)^2 := by
    have h : row ≤ cap*cap+cap := Nat.add_le_add hprod hv
    exact h.trans (by nlinarith)
  have hm₀b : (6*u+13)*cols ≤ (6*cap+13)*cap := by gcongr
  have hm₁b : (6*row+13)*width ≤ (6*(cap+1)^2+13)*cap := by gcongr
  refine ⟨_, hm₀.seq (hc₀.seq (hm₁.seq hc₁)), ?_⟩
  unfold denseIndicesBound
  omega

end FourToOneGames.SATMachine

end

/- SATEdgePrepare -/
section

set_option autoImplicit false
set_option Elab.async false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity WordMachines
open WordMachines.LiftInput (appendLeft_exec)

def edgeCellStore (P : LabelCover) (u v a : ℕ) (out : List BSym) : Fin 41 → List BSym :=
  conflictStore P u v a 0 0 0 0 [] out

private def addressPorts : Fin 9 ↪ Fin 21 := ⟨![5,2,6,3,7,8,9,10,11], by decide⟩

noncomputable def prepareEdgeCell : StackProg (Fin 41) BSym :=
  .seq (onPorts (Fin.castAddEmb 20) (onPorts addressPorts denseIndices))
    (.seq (queryTable 0 8 18 12 readSymbol) (queryTable 1 9 18 13 (lookupField .one)))

def prepareEdgeCellBound (cap : ℕ) : ℕ :=
  denseIndicesBound cap + queryTableBound cap cap (15*cap+11) +
    queryTableBound cap cap (20*cap+15) + 2

set_option maxHeartbeats 2500000 in
theorem prepareEdgeCell_exec (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR)
    (a : Fin P.sizeL) (out : List BSym) (cap : ℕ)
    (hu : u.val ≤ cap) (hv : v.val ≤ cap) (ha : a.val ≤ cap)
    (hc : P.nR ≤ cap) (hw : P.sizeL ≤ cap)
    (hAdj : (nativeAdjacency P).length ≤ cap) (hProj : (nativeProjection P).length ≤ cap) :
    let row := u.val*P.nR+v.val
    let field := row*P.sizeL+a.val
    let flag := nativeBit (decide ((u,v) ∈ P.edges))
    ∃ t, prepareEdgeCell.Exec (edgeCellStore P u.val v.val a.val out)
      (conflictStore P u.val v.val a.val 0 row field (P.proj u v a).val [flag] out) t ∧
      t ≤ prepareEdgeCellBound cap := by
  dsimp only
  let row := u.val*P.nR+v.val
  let field := row*P.sizeL+a.val
  let flag := nativeBit (decide ((u,v) ∈ P.edges))
  let target := (P.proj u v a).val
  let parent := conflictParent P u.val v.val a.val 0
  let empty := fun _ : Fin 20 => ([] : List BSym)
  let base := parent 0 0 0 [] [] out
  let first := parent row field 0 [] [] out
  let second := parent row field 0 [flag] [] out
  let third := parent row field target [flag] [] out
  obtain ⟨t, ht, htb⟩ := denseIndices_exec u.val P.nR v.val P.sizeL a.val cap hu hc hv hw ha
  have hFirst : first = Function.update
      (Function.update base 8 (List.replicate row BSym.one)) 9 (List.replicate field BSym.one) :=
    funext (fun k => by fin_cases k <;> rfl)
  have hindices : (onPorts addressPorts denseIndices).Exec base first t := by
    apply onPorts_exec addressPorts ht
    · intro k
      fin_cases k <;> rfl
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      have h₈ : k ≠ 8 := (hk 5).symm
      have h₉ : k ≠ 9 := (hk 6).symm
      simp only [hFirst, Function.update_of_ne h₈, Function.update_of_ne h₉]
  have hRow := (nativeAdjacency_address_lt P u v).le.trans hAdj
  have hField := (nativeProjection_address_lt P u v a).le.trans hProj
  let rowIndex := List.replicate row BSym.one
  let fieldIndex := List.replicate field BSym.one
  have hrow : row ≤ cap := hRow
  have hfield : field ≤ cap := hField
  have hReadAdj := nativeAdjacency_read P u v
  let adjEnd := lookupStore (flag :: (nativeAdjacency P).drop (row+1)) rowIndex [flag]
  obtain ⟨x, hx, hxb⟩ := queryTable_exec first 0 8 18 12 readSymbol adjEnd [flag]
    (15*row+11) (15*cap+11) rfl (by decide) (by decide) (by decide)
    hReadAdj rfl (by omega)
  have hAdjEffect : Function.update first 12 ([flag] ++ first 12) = second :=
    funext (fun k => by fin_cases k <;> rfl)
  rw [hAdjEffect] at hx
  obtain ⟨y, hy, hyb⟩ := nativeProjection_read P u v a []
  simp only [List.append_nil] at hy
  let projEnd := lookupStore (nativeProjection P) fieldIndex (List.replicate target .one)
  have hyBudget : y ≤ 20*cap+15 := by
    change y ≤ 10*(nativeProjection P).length+10*field+15 at hyb
    omega
  obtain ⟨z, hz, hzb⟩ := queryTable_exec second 1 9 18 13 (lookupField .one)
    projEnd (List.replicate target .one) y (20*cap+15)
    rfl (by decide) (by decide) (by decide) hy rfl hyBudget
  have hProjEffect : Function.update second 13 (List.replicate target .one ++ second 13) = third := by
    rw [show second 13 = [] from rfl, List.append_nil]
    exact funext (fun k => by fin_cases k <;> rfl)
  rw [hProjEffect] at hz
  refine ⟨_, (appendLeft_exec hindices empty).seq (hx.seq hz), ?_⟩
  have hxb' : x ≤ queryTableBound cap cap (15*cap+11) := by
    change x ≤ queryTableBound (nativeAdjacency P).length (List.replicate row BSym.one).length
      (15*cap+11) at hxb
    simp only [List.length_replicate, queryTableBound] at hxb ⊢
    omega
  have hzb' : z ≤ queryTableBound cap cap (20*cap+15) := by
    change z ≤ queryTableBound (nativeProjection P).length (List.replicate field BSym.one).length
      (20*cap+15) at hzb
    simp only [List.length_replicate, queryTableBound] at hzb ⊢
    omega
  unfold prepareEdgeCellBound
  omega

end FourToOneGames.SATMachine

end

/- SATEdgeCell -/
section

set_option autoImplicit false
set_option Elab.async false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity WordMachines
open WordMachines.LiftInput (appendLeft_exec)

private def edgeWorkPorts : Fin 4 ↪ Fin 21 := ⟨![8,9,12,13], by decide⟩

private noncomputable def clearEdgeWork : StackProg (Fin 41) BSym :=
  onPorts (Fin.castAddEmb 20) (onPorts edgeWorkPorts (BankCalls.clearBank 4 BSym))

set_option maxHeartbeats 2500000 in
private theorem clearEdgeWork_exec (P : LabelCover) (u v a row field expected cap : ℕ)
    (flag : BSym) (out : List BSym) (hr : row ≤ cap) (hf : field ≤ cap) (he : expected ≤ cap)
    (hcap : 1 ≤ cap) :
    ∃ t, clearEdgeWork.Exec (conflictStore P u v a 0 row field expected [flag] out)
      (edgeCellStore P u v a out) t ∧ t ≤ 3*cap+1 := by
  let before := conflictParent P u v a 0 row field expected [flag] [] out
  let after := conflictParent P u v a 0 0 0 0 [] [] out
  have h (k : Fin 4) : (before (edgeWorkPorts k)).length ≤ cap := by
    fin_cases k
    · change (List.replicate row BSym.one).length ≤ cap
      simpa only [List.length_replicate] using hr
    · change (List.replicate field BSym.one).length ≤ cap
      simpa only [List.length_replicate] using hf
    · exact hcap
    · change (List.replicate expected BSym.one).length ≤ cap
      simpa only [List.length_replicate] using he
  obtain ⟨t, ht, hb⟩ := BankCalls.clearBank_exec (fun k => before (edgeWorkPorts k)) cap h
  have hupdate : before = Function.update (Function.update (Function.update (Function.update after
      8 (List.replicate row BSym.one)) 9 (List.replicate field BSym.one)) 12 [flag])
      13 (List.replicate expected BSym.one) := funext (fun k => by fin_cases k <;> rfl)
  have hr : (onPorts edgeWorkPorts (BankCalls.clearBank 4 BSym)).Exec before after t := by
    refine onPorts_exec edgeWorkPorts ht (fun _ => rfl) ?_ ?_
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      have h₈ : k ≠ 8 := (hk 0).symm
      have h₉ : k ≠ 9 := (hk 1).symm
      have h₁₂ : k ≠ 12 := (hk 2).symm
      have h₁₃ : k ≠ 13 := (hk 3).symm
      simp only [hupdate, Function.update_of_ne h₈, Function.update_of_ne h₉,
        Function.update_of_ne h₁₂, Function.update_of_ne h₁₃]
  exact ⟨t, appendLeft_exec hr (fun _ : Fin 20 => []), hb⟩

private def edgePresent (h : Fin 41 → Option BSym) : Bool := h 12 == some BSym.one
private def skipCell : StackProg (Fin 41) BSym := .act (fun _ _ => .keep)

/-- Emit the forbidden-pair clauses for one left label of one dense edge cell. -/
noncomputable def edgeCell (writer : StackProg (Fin 5) BSym) : StackProg (Fin 41) BSym :=
  .seq prepareEdgeCell (.seq (.branch edgePresent (conflictLabels writer) skipCell) clearEdgeWork)

def edgeCellWord (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR) (a : Fin P.sizeL) : List BSym :=
  if (u,v) ∈ P.edges then conflictLabelsWord u.val v.val a.val (P.proj u v a).val P.sizeR else []

def edgeCellBound (C cap : ℕ) : ℕ := prepareEdgeCellBound cap + conflictLabelsBound C cap + 3*cap+5

theorem edgeCell_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR)
    (a : Fin P.sizeL) (out : List BSym) (hL : P.nL ≤ cap) (hR : P.nR ≤ cap)
    (hWL : P.sizeL ≤ cap) (hWR : P.sizeR ≤ cap) (hcap : 1 ≤ cap)
    (hAdj : (nativeAdjacency P).length ≤ cap) (hProj : (nativeProjection P).length ≤ cap) :
    ∃ t, (edgeCell writer).Exec (edgeCellStore P u.val v.val a.val out)
      (edgeCellStore P u.val v.val a.val (edgeCellWord P u v a ++ out)) t ∧ t ≤ edgeCellBound C cap := by
  let row := u.val*P.nR+v.val
  let field := row*P.sizeL+a.val
  let target := (P.proj u v a).val
  let flag := nativeBit (decide ((u,v) ∈ P.edges))
  let prep := conflictStore P u.val v.val a.val 0 row field target [flag]
  let out' := edgeCellWord P u v a ++ out
  have hu := u.isLt.le.trans hL
  have hv := v.isLt.le.trans hR
  have ha := a.isLt.le.trans hWL
  have he := (P.proj u v a).isLt.le.trans hWR
  obtain ⟨t, ht, htb⟩ := prepareEdgeCell_exec P u v a out cap hu hv ha hR hWL hAdj hProj
  obtain ⟨r, hr, hrb⟩ := clearEdgeWork_exec P u.val v.val a.val row field target cap flag out'
    ((nativeAdjacency_address_lt P u v).le.trans hAdj)
    ((nativeProjection_address_lt P u v a).le.trans hProj) he hcap
  have hbranch : ∃ b, (StackProg.branch edgePresent (conflictLabels writer) skipCell).Exec
      (prep out) (prep out') b ∧ b ≤ conflictLabelsBound C cap+1 := by
    by_cases hm : (u,v) ∈ P.edges
    · have hg : edgePresent (fun k => (prep out k).head?) = true := by
        change (some flag == some BSym.one) = true
        simp [flag, hm, nativeBit]
      obtain ⟨b, hb, hbb⟩ := conflictLabels_exec writer C cap hw P u.val v.val a.val row field
        target [flag] out hu hv ha hWR he hcap
      have ho : out' = conflictLabelsWord u.val v.val a.val target P.sizeR ++ out := by
        simp [out', edgeCellWord, hm, target]
      rw [ho]
      exact ⟨_, StackProg.Exec.branchTrue (q := skipCell) hg hb, by omega⟩
    · have hg : edgePresent (fun k => (prep out k).head?) = false := by
        change (some flag == some BSym.one) = false
        simp [flag, hm, nativeBit]
      have ho : out' = out := by simp [out', edgeCellWord, hm]
      rw [ho]
      have hs : skipCell.Exec (prep out) (prep out) 1 := by
        unfold skipCell
        convert StackProg.Exec.act (fun _ _ => .keep) (prep out) using 1
        exact funext (fun _ => rfl)
      exact ⟨_, StackProg.Exec.branchFalse (p := conflictLabels writer) hg hs,
        by unfold conflictLabelsBound; omega⟩
  obtain ⟨b, hb, hbb⟩ := hbranch
  refine ⟨_, ht.seq (hb.seq hr), ?_⟩
  unfold edgeCellBound
  omega

end FourToOneGames.SATMachine

end

/- ProjectionTraversal -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines

open CookPvsNP

variable {K A : Type} [DecidableEq K]

private def rectanglePorts (ports : Fin 8 ↪ K) : Fin 5 ↪ K :=
  (Fin.castAddEmb 3).trans ports

/-- The rectangle ports are followed by the label counter, its limit, and its copy scratch tape. -/
def projectionFrame (ports : Fin 8 ↪ K) (frame : K → List A) (token : A)
    (row col label : ℕ) (out : List A) : K → List A :=
  countFrame
    (Function.update (Function.update frame (ports 0) (List.replicate row token))
      (ports 1) (List.replicate col token))
    (ports 5) (ports 2) token label out

private def labelLoop (ports : Fin 8 ↪ K) (body : StackProg K A) : StackProg K A :=
  .seq (copyProg (ports 6) (ports 5) (ports 7)) (emitCounted (ports 5) body)

def emitProjectionTable (ports : Fin 8 ↪ K) (body : StackProg K A) : StackProg K A :=
  emitRectangle (rectanglePorts ports) (labelLoop ports body)

private theorem label_zero (ports : Fin 8 ↪ K) (frame : K → List A)
    (token : A) (row col : ℕ) (out : List A) :
    projectionFrame ports frame token row col 0 out =
      rectangleFrame (rectanglePorts ports) (Function.update frame (ports 5) [])
        token row col out := by
  unfold projectionFrame rectangleFrame countFrame
  change Function.update
    (Function.update (Function.update (Function.update frame (ports 0) (List.replicate row token))
      (ports 1) (List.replicate col token)) (ports 5) []) (ports 2) out =
    Function.update (Function.update (Function.update (Function.update frame (ports 5) [])
      (ports 0) (List.replicate row token)) (ports 1) (List.replicate col token)) (ports 2) out
  rw [Function.update_comm (ports.injective.ne (by decide : (1 : Fin 8) ≠ 5)),
    Function.update_comm (ports.injective.ne (by decide : (0 : Fin 8) ≠ 5))]

private theorem fillLabels_exec (ports : Fin 8 ↪ K) (frame : K → List A)
    (token : A) (row col labels : ℕ) (out : List A)
    (hlimit : frame (ports 6) = List.replicate labels token) (hscratch : frame (ports 7) = []) :
    (copyProg (ports 6) (ports 5) (ports 7)).Exec
      (projectionFrame ports frame token row col 0 out)
      (projectionFrame ports frame token row col labels out) (6*labels+3) := by
  let src := projectionFrame ports frame token row col 0 out
  have hl : src (ports 6) = List.replicate labels token := by
    simp [src, projectionFrame, countFrame, ports.injective.eq_iff, hlimit]
  have h₀ : src (ports 5) = [] := by
    simp [src, projectionFrame, countFrame, ports.injective.eq_iff]
  have hw : src (ports 7) = [] := by
    simp [src, projectionFrame, countFrame, ports.injective.eq_iff, hscratch]
  have hupdate : Function.update src (ports 5) (src (ports 6) ++ src (ports 5)) =
      projectionFrame ports frame token row col labels out := by
    rw [hl, h₀, List.append_nil]
    unfold src projectionFrame countFrame
    rw [Function.update_comm (ports.injective.ne (by decide : (2 : Fin 8) ≠ 5)),
      Function.update_idem]
  have hcopy := stack_copy (ports 6) (ports 5) (ports 7)
    (ports.injective.ne (by decide)) (ports.injective.ne (by decide))
    (ports.injective.ne (by decide)) src hw
  rw [hupdate] at hcopy
  simpa only [hl, List.length_replicate] using hcopy

/-- Emit the projection fields in lexicographic vertex and label order. -/
theorem emitProjectionTable_exec (ports : Fin 8 ↪ K) (frame : K → List A)
    (token : A) (rows cols labels : ℕ) (body : StackProg K A) (entry : ℕ → ℕ → ℕ → List A)
    (budget : ℕ) (tail : List A)
    (hcols : frame (ports 3) = List.replicate cols token) (hcolWork : frame (ports 4) = [])
    (hlabels : frame (ports 6) = List.replicate labels token) (hlabelWork : frame (ports 7) = [])
    (hbody : ∀ i < rows, ∀ j < cols, ∀ a < labels, ∀ out : List A, ∃ steps,
      body.Exec (projectionFrame ports frame token i j a out)
        (projectionFrame ports frame token i j a (entry i j a ++ out)) steps ∧ steps ≤ budget) :
    ∃ t, (emitProjectionTable ports body).Exec (projectionFrame ports frame token rows 0 0 tail)
      (projectionFrame ports frame token 0 0 0 (rectangleWords
        (fun i j => ascendingWords (entry i j) labels) rows cols ++ tail)) t ∧
      t ≤ rows * (cols * (labels*(budget+4)+6*labels+9) + 6*cols + 9) + 1 := by
  have hcell (i : ℕ) (hi : i < rows) (j : ℕ) (hj : j < cols) (out : List A) :
      ∃ t, (labelLoop ports body).Exec
        (projectionFrame ports frame token i j 0 out)
        (projectionFrame ports frame token i j 0 (ascendingWords (entry i j) labels ++ out)) t ∧
        t ≤ labels * (budget+4) + 6*labels + 5 := by
    obtain ⟨u, hu, hub⟩ := emitCounted_exec
      (Function.update (Function.update frame (ports 0) (List.replicate i token))
        (ports 1) (List.replicate j token))
      (ports 5) (ports 2) (ports.injective.ne (by decide)) token body (entry i j)
      labels budget (hbody i hi j hj) out
    exact ⟨_, (fillLabels_exec ports frame token i j labels out hlabels hlabelWork).seq hu, by omega⟩
  have hc : Function.update frame (ports 5) [] (rectanglePorts ports 3) =
      List.replicate cols token := by
    change Function.update frame (ports 5) [] (ports 3) = _
    simpa [ports.injective.eq_iff] using hcols
  have hw : Function.update frame (ports 5) [] (rectanglePorts ports 4) = [] := by
    change Function.update frame (ports 5) [] (ports 4) = _
    simpa [ports.injective.eq_iff] using hcolWork
  have h := emitRectangle_exec (rectanglePorts ports) (Function.update frame (ports 5) [])
    token rows cols (labelLoop ports body) (fun i j => ascendingWords (entry i j) labels)
    (labels*(budget+4)+6*labels+5) tail hc hw
    (fun i hi j hj out => by simpa only [label_zero] using hcell i hi j hj out)
  simpa only [label_zero, emitProjectionTable, Nat.add_assoc, show 5+4=9 by decide] using h

end FourToOneGames.WordMachines

end

/- SATConstraintTraversal -/
section

set_option autoImplicit false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity WordMachines

private def clauseTablePorts : Fin 8 ↪ Fin 41 := ⟨![5,6,17,2,18,7,3,19], by decide⟩

private theorem edgeCellFrame (P : LabelCover) (u v a : ℕ) (out : List BSym) :
    projectionFrame clauseTablePorts (edgeCellStore P 0 0 0 []) .one u v a out =
      edgeCellStore P u v a out := by
  unfold projectionFrame countFrame
  change Function.update (Function.update (Function.update (Function.update (edgeCellStore P 0 0 0 [])
    ((5 : Fin 21).castAdd 20) (List.replicate u BSym.one))
    ((6 : Fin 21).castAdd 20) (List.replicate v BSym.one))
    ((7 : Fin 21).castAdd 20) (List.replicate a BSym.one)) ((17 : Fin 21).castAdd 20) out = _
  unfold edgeCellStore conflictStore
  rw [BankCalls.append_update_left, BankCalls.append_update_left,
    BankCalls.append_update_left, BankCalls.append_update_left]
  congr 1
  exact funext (fun k => by fin_cases k <;> rfl)

private def edgeCellAt (P : LabelCover) (u v a : ℕ) : List BSym :=
  if hu : u < P.nL then
    if hv : v < P.nR then
      if ha : a < P.sizeL then edgeCellWord P ⟨u,hu⟩ ⟨v,hv⟩ ⟨a,ha⟩ else []
    else []
  else []

def constraintWord (P : LabelCover) : List BSym :=
  rectangleWords (fun u v => ascendingWords (edgeCellAt P u v) P.sizeL) P.nL P.nR

noncomputable def constraintTable (writer : StackProg (Fin 5) BSym) : StackProg (Fin 41) BSym :=
  emitProjectionTable clauseTablePorts (edgeCell writer)

def constraintTableBound (C cap : ℕ) : ℕ :=
  cap*(cap*(cap*(edgeCellBound C cap+4)+6*cap+9)+6*cap+9)+1

theorem constraintTable_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (P : LabelCover) (tail : List BSym)
    (hL : P.nL ≤ cap) (hR : P.nR ≤ cap) (hWL : P.sizeL ≤ cap) (hWR : P.sizeR ≤ cap)
    (hcap : 1 ≤ cap) (hAdj : (nativeAdjacency P).length ≤ cap)
    (hProj : (nativeProjection P).length ≤ cap) :
    ∃ t, (constraintTable writer).Exec (edgeCellStore P P.nL 0 0 tail)
      (edgeCellStore P 0 0 0 (constraintWord P ++ tail)) t ∧ t ≤ constraintTableBound C cap := by
  obtain ⟨t, ht, hb⟩ := emitProjectionTable_exec clauseTablePorts (edgeCellStore P 0 0 0 [])
    BSym.one P.nL P.nR P.sizeL (edgeCell writer) (edgeCellAt P) (edgeCellBound C cap)
    tail rfl rfl rfl rfl (fun u hu v hv a ha out => by
      simp only [edgeCellFrame, edgeCellAt, dif_pos hu, dif_pos hv, dif_pos ha]
      exact edgeCell_exec writer C cap hw P ⟨u,hu⟩ ⟨v,hv⟩ ⟨a,ha⟩ out
        hL hR hWL hWR hcap hAdj hProj)
  refine ⟨t, by simpa only [edgeCellFrame, constraintTable, constraintWord] using ht, hb.trans ?_⟩
  unfold constraintTableBound
  gcongr

private theorem finRange_flatMap {A : Type} (n : ℕ) (f : ℕ → List A) :
    (List.finRange n).flatMap (fun i => f i.val) = ascendingWords f n := by
  have h : (List.finRange n).map (fun i => i.val) = List.range n := by
    apply List.ext_getElem <;> simp
  calc
    _ = ((List.finRange n).map (fun i => i.val)).flatMap f := (List.flatMap_map _ _ _).symm
    _ = ascendingWords f n := congrArg (List.flatMap f) h

private theorem flatMap_filtered {A B : Type} (keep : A → Bool) (word : A → List B) (xs : List A) :
    (xs.filter keep).flatMap word = xs.flatMap (fun x => if keep x then word x else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : keep x <;> simp [h, ih]

private theorem conflictLabels_spec (P : LabelCover) (u : Fin P.nL) (v : Fin P.nR)
    (a : Fin P.sizeL) :
    (((List.finRange P.sizeR).filter fun b => decide (P.proj u v a ≠ b)).map
      (fun b => conflictClause u.val v.val a.val b.val)).flatMap clauseWord =
        conflictLabelsWord u.val v.val a.val (P.proj u v a).val P.sizeR := by
  rw [List.flatMap_map, flatMap_filtered]
  unfold conflictLabelsWord
  rw [← finRange_flatMap]
  apply List.flatMap_congr
  intro b _
  by_cases h : (P.proj u v a).val = b.val
  · have he : P.proj u v a = b := Fin.ext h
    simp [he, conflictTrialWord]
  · have he : P.proj u v a ≠ b := fun e => h (congrArg Fin.val e)
    simp [h, he, conflictTrialWord]

theorem constraintWord_spec (P : LabelCover) :
    ((List.finRange P.nL).flatMap fun u =>
      (List.finRange P.nR).flatMap fun v =>
        if (u,v) ∈ P.edges then
          (List.finRange P.sizeL).flatMap fun a =>
            ((List.finRange P.sizeR).filter fun b => decide (P.proj u v a ≠ b)).map
              (fun b => conflictClause u.val v.val a.val b.val)
        else []).flatMap clauseWord = constraintWord P := by
  unfold constraintWord rectangleWords
  rw [← finRange_flatMap P.nL, List.flatMap_assoc]
  apply List.flatMap_congr
  intro u _
  rw [← finRange_flatMap P.nR, List.flatMap_assoc]
  apply List.flatMap_congr
  intro v _
  change _ = ascendingWords (edgeCellAt P u.val v.val) P.sizeL
  rw [← finRange_flatMap P.sizeL]
  by_cases hm : (u,v) ∈ P.edges
  · simp only [if_pos hm, List.flatMap_assoc]
    apply List.flatMap_congr
    intro a _
    simpa only [edgeCellAt, dif_pos u.isLt, dif_pos v.isLt, dif_pos a.isLt, edgeCellWord, if_pos hm]
      using conflictLabels_spec P u v a
  · simp [hm, edgeCellAt, u.isLt, v.isLt, edgeCellWord]

def emptyGameWord : List BSym :=
  clauseWord (constantUnitClause true) ++ clauseWord (constantUnitClause false)

theorem formulaWord_layout (P : LabelCover) :
    formulaWord (satFormula P) = if P.edges.Nonempty then
      vertexSideWord 0 P.nL P.sizeL ++ vertexSideWord 1 P.nR P.sizeR ++ constraintWord P
    else emptyGameWord := by
  unfold formulaWord
  rw [satFormula_layout]
  by_cases h : P.edges.Nonempty
  · simp only [if_pos h, List.flatMap_append, vertexSideWord_spec, constraintWord_spec]
  · simp [h, emptyGameWord]

end FourToOneGames.SATMachine

end

/- SATMainPasses -/
section

set_option autoImplicit false
set_option Elab.async false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity WordMachines WordMachines.BankCalls
open WordMachines.LiftInput (appendLeft_exec)

structure SATInputBound (P : LabelCover) (cap : ℕ) : Prop where
  leftCount : P.nL ≤ cap
  rightCount : P.nR ≤ cap
  leftWidth : P.sizeL ≤ cap
  rightWidth : P.sizeR ≤ cap
  adjacency : (nativeAdjacency P).length ≤ cap
  projection : (nativeProjection P).length ≤ cap
  positive : 1 ≤ cap

theorem satInputBound_length (P : LabelCover) : SATInputBound P ((encodeLabelCover P).length+1) := by
  have h := congrArg List.length (labelCover_input_layout P)
  simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.length_nil,
    unary, List.length_replicate, List.length_cons] at h
  have hAdj : (nativeAdjacency P).length = (adjacencyBits P).length := List.length_map nativeBit
  have hProj : (nativeProjection P).length =
      ((projectionWords P).flatMap (unary true false)).length := List.length_map nativeBit
  constructor <;> omega

/-- Hold the decoded instance and the shared output stack outside the private work bank. -/
def satParent (P : LabelCover) (one flag out : List BSym) : Fin 12 → List BSym :=
  ![nativeProjection P, List.replicate P.nL .one, List.replicate P.nR .one,
    List.replicate P.sizeL .one, List.replicate P.sizeR .one,
    List.replicate (P.nL*P.nR) .one, nativeAdjacency P, one, flag, [], out, []]

def satStore (P : LabelCover) (one flag out : List BSym) : Fin 53 → List BSym :=
  Fin.append (satParent P one flag out) (fun _ : Fin 41 => [])

def satPassBound (cap budget : ℕ) : ℕ := 10*(7*(6*cap+4)+1)+10*budget+7

private theorem callBound (p : Fin 12 → List BSym) (slots : List (Fin 12 × Fin 41))
    (cap budget t : ℕ) (hsize : slots.length ≤ 7)
    (hreads : ∀ sd ∈ slots, (p sd.1).length ≤ cap)
    (h : t ≤ 10*copyCost p slots+10*budget+7) : t ≤ satPassBound cap budget := by
  have he := copyCost_le p slots cap hreads
  have hm := Nat.mul_le_mul_right (6*cap+4) hsize
  unfold satPassBound
  omega

private def constraintInputs : List (Fin 12 × Fin 41) :=
  [(6,0),(0,1),(2,2),(3,3),(4,4),(1,5),(7,15)]

noncomputable def satConstraints (writer : StackProg (Fin 5) BSym) : StackProg (Fin 53) BSym :=
  callBank 11 10 17 constraintInputs (constraintTable writer)

set_option maxHeartbeats 2500000 in
theorem satConstraints_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (P : LabelCover) (flag out : List BSym) (h : SATInputBound P cap) :
    ∃ t, (satConstraints writer).Exec (satStore P [.one] flag out)
      (satStore P [.one] flag (constraintWord P ++ out)) t ∧
      t ≤ satPassBound cap (constraintTableBound C cap) := by
  let parent := satParent P [.one] flag out
  have hload : copiedInputs parent constraintInputs (fun _ => []) = edgeCellStore P P.nL 0 0 [] := by
    exact funext (fun k => by fin_cases k <;>
      simp [copiedInputs, constraintInputs, parent, satParent] <;> rfl)
  obtain ⟨r, hr, hrb⟩ := constraintTable_exec writer C cap hw P []
    h.leftCount h.rightCount h.leftWidth h.rightWidth h.positive h.adjacency h.projection
  simp only [List.append_nil] at hr
  have hslots : ∀ sd ∈ constraintInputs, sd.1 ≠ (11 : Fin 12) := by
    simp [constraintInputs]
  obtain ⟨t, ht, htb⟩ := callBank_exec parent 11 10 17 constraintInputs
    (constraintTable writer) (edgeCellStore P 0 0 0 (constraintWord P))
    (constraintWord P) r (constraintTableBound C cap) rfl (by decide) hslots
    (by rw [hload]; exact hr) rfl hrb
  have he : Function.update parent 10 (constraintWord P ++ parent 10) =
      satParent P [.one] flag (constraintWord P ++ out) :=
    funext (fun k => by fin_cases k <;> rfl)
  rw [he] at ht
  refine ⟨t, ht, callBound parent constraintInputs cap _ t (by decide) ?_ htb⟩
  intro sd hsd
  simp [constraintInputs] at hsd
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [parent, satParent, h.adjacency, h.projection, h.leftCount, h.rightCount,
      h.leftWidth, h.rightWidth, h.positive]

private def sideInputs (right : Bool) : List (Fin 12 × Fin 41) :=
  [(if right then 7 else 9,0), (if right then 2 else 1,1), (if right then 4 else 3,2), (7,6)]

noncomputable def satVertices (writer : StackProg (Fin 5) BSym) (right : Bool) :
    StackProg (Fin 53) BSym :=
  callBank 11 10 7 (sideInputs right) (onPorts (Fin.castAddEmb 12) (vertexSide writer))

set_option maxHeartbeats 2500000 in
theorem satVertices_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (P : LabelCover) (right : Bool) (flag out : List BSym)
    (h : SATInputBound P cap) :
    let count := if right then P.nR else P.nL
    let width := if right then P.sizeR else P.sizeL
    ∃ t, (satVertices writer right).Exec (satStore P [.one] flag out)
      (satStore P [.one] flag (vertexSideWord right.toNat count width ++ out)) t ∧
      t ≤ satPassBound cap (vertexSideBound C cap) := by
  dsimp only
  let count := if right then P.nR else P.nL
  let width := if right then P.sizeR else P.sizeL
  let parent := satParent P [.one] flag out
  let empty := fun _ : Fin 12 => ([] : List BSym)
  let word := vertexSideWord right.toNat count width
  have hload : copiedInputs parent (sideInputs right) (fun _ => []) =
      Fin.append (choiceStore right.toNat count width 0 []) empty := by
    cases right <;> exact funext (fun k => by fin_cases k <;>
      simp [copiedInputs, sideInputs, parent, satParent, count, width] <;> rfl)
  obtain ⟨r, hr, hrb⟩ := vertexSide_exec writer C cap hw right.toNat count width []
    ((Bool.toNat_le right).trans h.positive)
    (by cases right <;> first | exact h.leftCount | exact h.rightCount)
    (by cases right <;> first | exact h.leftWidth | exact h.rightWidth) h.positive
  simp only [List.append_nil] at hr
  have hslots : ∀ sd ∈ sideInputs right, sd.1 ≠ (11 : Fin 12) := by
    cases right <;> simp [sideInputs]
  obtain ⟨t, ht, htb⟩ := callBank_exec parent 11 10 7 (sideInputs right)
    (onPorts (Fin.castAddEmb 12) (vertexSide writer))
    (Fin.append (choiceStore right.toNat 0 width 0 word) empty)
    word r (vertexSideBound C cap) rfl (by decide) hslots
    (by rw [hload]; exact appendLeft_exec hr empty) rfl hrb
  have he : Function.update parent 10 (word ++ parent 10) = satParent P [.one] flag (word ++ out) :=
    funext (fun k => by fin_cases k <;> rfl)
  rw [he] at ht
  refine ⟨t, ht, callBound parent (sideInputs right) cap _ t (by cases right <;> decide) ?_ htb⟩
  intro sd hsd
  cases right <;> simp [sideInputs] at hsd <;>
    rcases hsd with rfl | rfl | rfl | rfl <;>
    simp [parent, satParent, h.leftCount, h.rightCount, h.leftWidth, h.rightWidth, h.positive]

end FourToOneGames.SATMachine

end

/- SATAssembly -/
section

set_option autoImplicit false
set_option Elab.async false

namespace FourToOneGames.SATMachine

open CookPvsNP ProjSchedTW.Complexity Turing WordMachines
open WordMachines.LiftInput (appendLeft_exec)

private theorem nativeLoaded (P : LabelCover) :
    StackProgAlphabet.mapStore nativeBit (loadedStore P) =
      ![nativeProjection P, List.replicate P.nL .one, List.replicate P.nR .one,
        List.replicate P.sizeL .one, List.replicate P.sizeR .one,
        List.replicate (P.nL*P.nR) .one, nativeAdjacency P, [], [], []] := by
  funext k
  fin_cases k <;>
    first
    | rfl
    | change (List.replicate _ true).map nativeBit = List.replicate _ BSym.one
      simp [nativeBit]

private noncomputable def loadParent : StackProg (Fin 12) BSym :=
  onPorts (Fin.castAddEmb 2) nativeLoad

private noncomputable def loadSAT : StackProg (Fin 53) BSym :=
  onPorts (Fin.castAddEmb 41) loadParent

private theorem extendInit {A : Type} {n m : ℕ} (P : StackProg (Fin (n+m)) A)
    (Q : StackProg (Fin n) A) (k : Fin n) (w : List A) :
    (P.machine.init (k.castAdd m) w).store =
      Fin.append (Q.machine.init k w).store (fun _ : Fin m => []) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · by_cases hi : i = k
    · subst i
      simp [StackMachine.init]
    · have hne : i.castAdd m ≠ k.castAdd m :=
        fun he => hi (Fin.ext (congrArg (fun a : Fin (n+m) => a.val) he))
      simp [StackMachine.init, hi, hne]
  · have hne : i.natAdd n ≠ k.castAdd m := by
      intro he
      have hv : n+i.val = k.val := congrArg Fin.val he
      omega
    simp [StackMachine.init, hne]

private theorem loadSAT_exec (P : LabelCover) :
    ∃ t, loadSAT.Exec ((loadSAT.machine.init 0 ((encodeLabelCover P).map nativeBit)).store)
      (satStore P [] [] []) t ∧ t ≤ 18*(encodeLabelCover P).length+29 := by
  let w := (encodeLabelCover P).map nativeBit
  obtain ⟨n, hn, hb⟩ := nativeLoad_exec P
  rw [nativeLoaded] at hn
  have h := appendLeft_exec (appendLeft_exec hn (fun _ : Fin 2 => [])) (fun _ : Fin 41 => [])
  have hinit : (loadSAT.machine.init 0 w).store =
      Fin.append (Fin.append (nativeLoad.machine.init 0 w).store (fun _ : Fin 2 => []))
        (fun _ : Fin 41 => []) := by
    have h₁ : (loadSAT.machine.init 0 w).store =
        Fin.append (loadParent.machine.init 0 w).store (fun _ : Fin 41 => []) :=
      extendInit (n := 12) (m := 41) loadSAT loadParent 0 w
    have h₂ : (loadParent.machine.init 0 w).store =
        Fin.append (nativeLoad.machine.init 0 w).store (fun _ : Fin 2 => []) :=
      extendInit (n := 10) (m := 2) loadParent nativeLoad 0 w
    exact h₁.trans (congrArg (fun s : Fin 12 → List BSym => Fin.append s (fun _ : Fin 41 => [])) h₂)
  rw [← hinit] at h
  have hparent :
      Fin.append (![nativeProjection P, List.replicate P.nL .one, List.replicate P.nR .one,
        List.replicate P.sizeL .one, List.replicate P.sizeR .one,
        List.replicate (P.nL*P.nR) .one, nativeAdjacency P, [], [], []] : Fin 10 → List BSym)
        (fun _ : Fin 2 => []) = satParent P [] [] [] :=
    funext (fun k => by fin_cases k <;> rfl)
  rw [hparent] at h
  exact ⟨n, h, hb⟩

private def edgeDetectorPorts : Fin 4 ↪ Fin 12 := ⟨![6,8,9,11], by decide⟩

private noncomputable def edgeDetector : StackProg (Fin 12) BSym :=
  onPorts edgeDetectorPorts (StackProgAlphabet.mapProg nativeBit fromNativeBit anyTrue)

set_option maxHeartbeats 2000000 in
private theorem edgeDetector_exec (P : LabelCover) :
    ∃ t, edgeDetector.Exec (satParent P [.one] [] [])
      (satParent P [.one] [nativeBit (decide P.edges.Nonempty)] []) t ∧
      t ≤ 9*(nativeAdjacency P).length+9 := by
  obtain ⟨n, hn, hb⟩ := detectsEdge_exec P []
  have hinv : Function.LeftInverse fromNativeBit nativeBit := by
    intro x
    cases x <;> rfl
  have h := StackProgAlphabet.mapProg_exec nativeBit fromNativeBit hinv hn
  refine ⟨n, onPorts_exec edgeDetectorPorts h ?_ ?_ ?_, by simpa only [nativeAdjacency_length] using hb⟩
  · intro k
    fin_cases k <;> rfl
  · intro k
    fin_cases k <;> rfl
  · intro k hk
    have he : satParent P [.one] [nativeBit (decide P.edges.Nonempty)] [] =
        Function.update (satParent P [.one] [] []) 8 [nativeBit (decide P.edges.Nonempty)] :=
      funext (fun i => by fin_cases i <;> rfl)
    have hk' : k ≠ (8 : Fin 12) := (hk 1).symm
    simp only [he, Function.update_of_ne hk']

private def pushWord (dst : Fin 12) : List BSym → StackProg (Fin 12) BSym
  | [] => .act (fun _ _ => .keep)
  | b::bs => .seq (pushWord dst bs) (pushProg dst b)

private theorem pushWord_exec (p : Fin 12 → List BSym) (dst : Fin 12) (word : List BSym) :
    (pushWord dst word).Exec p (Function.update p dst (word ++ p dst)) (2*word.length+1) := by
  induction word with
  | nil =>
    convert StackProg.Exec.act (fun _ _ => .keep) p using 1 <;> (try simp) <;> rfl
  | cons b bs ih =>
    let next := Function.update p dst (bs ++ p dst)
    have hp := pushSymbol_exec dst b next
    have he : Function.update next dst (b :: next dst) =
        Function.update p dst ((b::bs) ++ p dst) := by simp [next, Function.update_idem]
    rw [he] at hp
    unfold pushWord
    exact ih.seq hp

private def hasEdgeFlag (h : Fin 53 → Option BSym) : Bool := h 8 == some BSym.one

private noncomputable def satNonempty (writer : StackProg (Fin 5) BSym) : StackProg (Fin 53) BSym :=
  .seq (satConstraints writer) (.seq (satVertices writer true) (satVertices writer false))

private noncomputable def satEmpty : StackProg (Fin 53) BSym :=
  onPorts (Fin.castAddEmb 41) (pushWord 10 emptyGameWord)

noncomputable def satProgram (writer : StackProg (Fin 5) BSym) : StackProg (Fin 53) BSym :=
  .seq loadSAT
    (.seq (onPorts (Fin.castAddEmb 41) (pushProg 7 .one))
      (.seq (onPorts (Fin.castAddEmb 41) edgeDetector)
        (.branch hasEdgeFlag (satNonempty writer) satEmpty)))

def satNonemptyBound (C cap : ℕ) : ℕ :=
  satPassBound cap (constraintTableBound C cap) + 2*satPassBound cap (vertexSideBound C cap)+2

private theorem satNonempty_exec (writer : StackProg (Fin 5) BSym) (C cap : ℕ)
    (hw : IsNumeralWriter writer C) (P : LabelCover) (flag : List BSym) (h : SATInputBound P cap) :
    ∃ t, (satNonempty writer).Exec (satStore P [.one] flag [])
      (satStore P [.one] flag
        (vertexSideWord 0 P.nL P.sizeL ++ vertexSideWord 1 P.nR P.sizeR ++ constraintWord P)) t ∧
      t ≤ satNonemptyBound C cap := by
  let constraints := constraintWord P
  let right := vertexSideWord 1 P.nR P.sizeR
  obtain ⟨a, ha, hab⟩ := satConstraints_exec writer C cap hw P flag [] h
  simp only [List.append_nil] at ha
  obtain ⟨b, hb, hbb⟩ := satVertices_exec writer C cap hw P true flag constraints h
  obtain ⟨c, hc, hcb⟩ := satVertices_exec writer C cap hw P false flag (right ++ constraints) h
  have hrun := ha.seq (hb.seq hc)
  refine ⟨a+1+(b+1+c), ?_, ?_⟩
  · simpa [satNonempty, right, constraints, List.append_assoc] using hrun
  · unfold satNonemptyBound
    omega

private theorem satEmpty_exec (P : LabelCover) (flag : List BSym) :
    satEmpty.Exec (satStore P [.one] flag []) (satStore P [.one] flag emptyGameWord)
      (2*emptyGameWord.length+1) := by
  let p := satParent P [.one] flag []
  have hp := pushWord_exec p 10 emptyGameWord
  have he : Function.update p 10 (emptyGameWord ++ p 10) = satParent P [.one] flag emptyGameWord := by
    exact funext (fun k => by fin_cases k <;> simp [p, satParent])
  rw [he] at hp
  exact appendLeft_exec hp (fun _ : Fin 41 => [])

def satProgramTime (C len : ℕ) : ℕ :=
  let cap := len+1
  30*cap+60 + satNonemptyBound C cap + 2*emptyGameWord.length+1

set_option maxHeartbeats 3000000 in
theorem satProgram_exec (writer : StackProg (Fin 5) BSym) (C : ℕ)
    (hw : IsNumeralWriter writer C) (P : LabelCover) :
    let w := (encodeLabelCover P).map nativeBit
    let flag := [nativeBit (decide P.edges.Nonempty)]
    ∃ t, (satProgram writer).Exec (((satProgram writer).machine.init 0 w).store)
      (satStore P [.one] flag (formulaWord (satFormula P))) t ∧ t ≤ satProgramTime C w.length := by
  dsimp only
  let w := (encodeLabelCover P).map nativeBit
  let cap := (encodeLabelCover P).length+1
  let flag := [nativeBit (decide P.edges.Nonempty)]
  have h := satInputBound_length P
  obtain ⟨a, ha, hab⟩ := loadSAT_exec P
  have hinit : (loadSAT.machine.init 0 w).store = ((satProgram writer).machine.init 0 w).store := rfl
  rw [hinit] at ha
  have hb := pushSymbol_exec 7 BSym.one (satParent P [] [] [])
  have he : Function.update (satParent P [] [] []) 7 [.one] = satParent P [.one] [] [] :=
    funext (fun k => by fin_cases k <;> rfl)
  change (pushProg 7 BSym.one).Exec (satParent P [] [] [])
    (Function.update (satParent P [] [] []) 7 [.one]) 1 at hb
  rw [he] at hb
  obtain ⟨c, hc, hcb⟩ := edgeDetector_exec P
  have hbranch : ∃ b, (StackProg.branch hasEdgeFlag (satNonempty writer) satEmpty).Exec
      (satStore P [.one] flag []) (satStore P [.one] flag (formulaWord (satFormula P))) b ∧
      b ≤ satNonemptyBound C cap + 2*emptyGameWord.length+2 := by
    by_cases hEdge : P.edges.Nonempty
    · have hguard : hasEdgeFlag (fun k => (satStore P [.one] flag [] k).head?) = true := by
        change (some (nativeBit (decide P.edges.Nonempty)) == some BSym.one) = true
        simp [hEdge, nativeBit]
      obtain ⟨b, hb, hbb⟩ := satNonempty_exec writer C cap hw P flag h
      rw [formulaWord_layout, if_pos hEdge]
      exact ⟨_, StackProg.Exec.branchTrue (q := satEmpty) hguard hb, by omega⟩
    · have hguard : hasEdgeFlag (fun k => (satStore P [.one] flag [] k).head?) = false := by
        change (some (nativeBit (decide P.edges.Nonempty)) == some BSym.one) = false
        simp [hEdge, nativeBit]
      rw [formulaWord_layout, if_neg hEdge]
      exact ⟨_, StackProg.Exec.branchFalse (p := satNonempty writer) hguard
        (satEmpty_exec P flag), by omega⟩
  obtain ⟨b, hf, hfb⟩ := hbranch
  let empty := fun _ : Fin 41 => ([] : List BSym)
  refine ⟨_, ha.seq ((appendLeft_exec hb empty).seq ((appendLeft_exec hc empty).seq hf)), ?_⟩
  have hAdj := h.adjacency
  change (nativeAdjacency P).length ≤ cap at hAdj
  have hload : a ≤ 18*cap+29 := by dsimp [cap]; omega
  dsimp only [satProgramTime, w]
  simp only [List.length_map]
  change _ ≤ 30*cap+60 + satNonemptyBound C cap+2*emptyGameWord.length+1
  omega

end FourToOneGames.SATMachine

end

/- LiftAdjacencyAtom -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.LiftOutput

open CookPvsNP OAI.PerfectCompleteness LiftInput Radix

def adjacencyStart {q : ℕ} (G : Instance q) (p u v : ℕ) (out : List Bool) : Fin 39 → List Bool :=
  Fin.append (cellFrame p u v (fun _ => 0) (fun _ => 0) 0)
    (adjacencyStore (recordBits G) 0 G.edges.length (2+2*q) 0 0 0 0 out [] [] [])

def adjacencyDecoded {q : ℕ} (G : Instance q) (p u v : ℕ) (out : List Bool) : Fin 39 → List Bool :=
  let e := ordinal p u v
  Fin.append (cellFrame p (u/p^3) (v/p^4) (digits u p 3) (digits v p 4) e)
    (adjacencyStore (recordBits G) e G.edges.length (2+2*q) (u/p^3) (v/p^4) 0 0 out [] [] [])

/-- Decode the two copied indices and emit the exact adjacency bit. -/
noncomputable def adjacencyAtom : StackProg (Fin 39) Bool :=
  .seq (onPorts (Fin.castAddEmb 20) cellIndexMachine)
    (.seq (copyProg 18 20 30) (.seq (copyProg 0 33 30) (.seq (copyProg 9 34 30)
      (onPorts (Fin.natAddEmb 19) emitAdjacencyBit))))

def adjacencyAtomBound (n count q p u v cap : ℕ) : ℕ :=
  3*(extractBound u p+1) + 4*(extractBound v p+1) + tagBound p +
    6*(p+u+v) + adjacencyValueBound n p count (2+2*q) u v cap + 17

private theorem copyUnaryRight_exec {n m : ℕ}
    (left : Fin n → List Bool) (right next : Fin m → List Bool)
    (src : Fin n) (dst scratch : Fin m) (hds : dst ≠ scratch) (hw : right scratch = [])
    (val : ℕ) (hs : left src = List.replicate val true) (hd : right dst = [])
    (hnext : Function.update right dst (List.replicate val true) = next) :
    (copyProg (src.castAdd m) (dst.natAdd n) (scratch.natAdd n)).Exec
      (Fin.append left right) (Fin.append left next) (6*val+3) := by
  simpa only [hs, hd, List.append_nil, List.length_replicate, hnext] using
    copyAppendRight_exec left right src dst scratch hds hw

theorem adjacencyAtom_exec {q : ℕ} (G : Instance q) (p u v : ℕ) (hp : 0 < p) (out : List Bool) :
    ∃ t, adjacencyAtom.Exec (adjacencyStart G p u v out)
      (adjacencyDecoded G p u v (edgeBit G p u v :: out)) t ∧
      t ≤ adjacencyAtomBound (recordBits G).length G.edges.length q p u v
        (G.leftVertices+G.rightVertices) := by
  let e := ordinal p u v
  let x := u/p^3
  let y := v/p^4
  let left := cellFrame p x y (digits u p 3) (digits v p 4) e
  let right := fun record l r =>
    adjacencyStore (recordBits G) record G.edges.length (2+2*q) l r 0 0 out [] [] []
  obtain ⟨t, ht, htb⟩ := cellIndexMachine_exec p u v hp
  have hdecode := appendLeft_exec ht (right 0 0 0)
  have he : (copyProg (18 : Fin 39) 20 30).Exec (Fin.append left (right 0 0 0))
      (Fin.append left (right e 0 0)) (6*e+3) :=
    copyUnaryRight_exec left (right 0 0 0) (right e 0 0) 18 1 11 (by decide) rfl e rfl rfl
      (funext (fun k => by fin_cases k <;> rfl))
  have hx : (copyProg (0 : Fin 39) 33 30).Exec (Fin.append left (right e 0 0))
      (Fin.append left (right e x 0)) (6*x+3) :=
    copyUnaryRight_exec left (right e 0 0) (right e x 0) 0 14 11 (by decide) rfl x rfl rfl
      (funext (fun k => by fin_cases k <;> rfl))
  have hy : (copyProg (9 : Fin 39) 34 30).Exec (Fin.append left (right e x 0))
      (Fin.append left (right e x y)) (6*y+3) :=
    copyUnaryRight_exec left (right e x 0) (right e x y) 9 15 11 (by decide) rfl y rfl rfl
      (funext (fun k => by fin_cases k <;> rfl))
  obtain ⟨s, hs, hsb⟩ := emitAdjacencyAt_exec G p u v out
  have hright := appendRight_exec hs left
  refine ⟨_, hdecode.seq (he.seq (hx.seq (hy.seq hright))), ?_⟩
  have he_le : e ≤ p := (Nat.mod_lt _ hp).le
  have hx_le : x ≤ u := Nat.div_le_self _ _
  have hy_le : y ≤ v := Nat.div_le_self _ _
  have hm : adjacencyValueBound (recordBits G).length e G.edges.length (2+2*q) x y
      (G.leftVertices+G.rightVertices) ≤
      adjacencyValueBound (recordBits G).length p G.edges.length (2+2*q) u v
        (G.leftVertices+G.rightVertices) := by
    unfold adjacencyValueBound RecordLookup.guardedBound RecordLookup.stepBound
    gcongr
  change s ≤ adjacencyValueBound (recordBits G).length e G.edges.length (2+2*q) x y
    (G.leftVertices+G.rightVertices) at hsb
  unfold adjacencyAtomBound
  omega

end FourToOneGames.WordMachines.LiftOutput

end

/- LiftEmitters -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.LiftOutput

open CookPvsNP OAI.PerfectCompleteness LiftInput BankCalls

/-- The preserved game registers, traversal counters, and constants shared by both output passes. -/
def emitterParent {q : ℕ} (G : Instance q) (p u v a : ℕ) (out : List Bool) : Fin 23 → List Bool :=
  Fin.append (withOutput (dimensionStore G p) out)
    ![List.replicate u true, List.replicate v true, List.replicate a true, [], [],
      List.replicate (2+2*q) true, [true,true]]

def emitterStore {q : ℕ} (G : Instance q) (p u v a : ℕ) (out : List Bool) : Fin 62 → List Bool :=
  Fin.append (emitterParent G p u v a out) (fun _ : Fin 39 => [])

private theorem updateOutput {q : ℕ} (G : Instance q) (p u v a : ℕ) (out next : List Bool) :
    Function.update (emitterParent G p u v a out) 15 next = emitterParent G p u v a next := by
  unfold emitterParent
  change Function.update (Fin.append (withOutput (dimensionStore G p) out) _)
    ((15 : Fin 16).castAdd 7) next = _
  rw [append_update_left, withOutput_update]

private def projectionInputs : List (Fin 23 × Fin 39) :=
  [(16,0),(5,1),(17,9),(5,10),(0,19),(21,21),(4,28),(18,33),(22,34)]

private def adjacencyInputs : List (Fin 23 × Fin 39) :=
  [(16,0),(5,1),(17,9),(5,10),(0,19),(21,21),(4,28)]

private noncomputable def projectionInBank : StackProg (Fin 39) Bool :=
  onPorts (Fin.castAddEmb 3) projectionAtom

noncomputable def emitProjectionCell : StackProg (Fin 62) Bool :=
  callBank 19 15 23 projectionInputs projectionInBank

noncomputable def emitAdjacencyCell : StackProg (Fin 62) Bool :=
  callBank 19 15 35 adjacencyInputs adjacencyAtom

def copyCap (n count q p u v a : ℕ) : ℕ := n+count+2*q+p+u+v+a+2

def projectionEmitterBound (n count q p u v a : ℕ) : ℕ :=
  10*(9*(6*copyCap n count q p u v a+4)+1) + 10*projectionAtomBound n count q p u v a + 7

def adjacencyEmitterBound (n count q p u v cap : ℕ) : ℕ :=
  10*(7*(6*copyCap n count q p u v 0+4)+1) + 10*adjacencyAtomBound n count q p u v cap + 7

private theorem loadedProjection {q : ℕ} (G : Instance q) (p u v a : ℕ) (out : List Bool) :
    copiedInputs (emitterParent G p u v a out) projectionInputs (fun _ => []) =
      Fin.append (projectionStart G p u v a []) (fun _ : Fin 3 => []) := by
  funext k
  fin_cases k <;> simp [copiedInputs, projectionInputs] <;> rfl

private theorem loadedAdjacency {q : ℕ} (G : Instance q) (p u v : ℕ) (out : List Bool) :
    copiedInputs (emitterParent G p u v 0 out) adjacencyInputs (fun _ => []) =
      adjacencyStart G p u v [] := by
  funext k
  fin_cases k <;> simp [copiedInputs, adjacencyInputs] <;> rfl

private theorem operandsBound {q : ℕ} (G : Instance q) (p u v a : ℕ) (out : List Bool) :
    let f := emitterParent G p u v a out
    ∀ i ∈ projectionInputs.map Prod.fst,
      (f i).length ≤ copyCap (recordBits G).length G.edges.length q p u v a := by
  dsimp only
  let f := emitterParent G p u v a out
  have h0 : f 0 = recordBits G := rfl
  have h4 : f 4 = List.replicate G.edges.length true := rfl
  have h5 : f 5 = List.replicate p true := rfl
  have h16 : f 16 = List.replicate u true := rfl
  have h17 : f 17 = List.replicate v true := rfl
  have h18 : f 18 = List.replicate a true := rfl
  have h21 : f 21 = List.replicate (2+2*q) true := rfl
  have h22 : f 22 = [true,true] := rfl
  change ∀ i ∈ projectionInputs.map Prod.fst, (f i).length ≤ _
  simp [projectionInputs, h0,h4,h5,h16,h17,h18,h21,h22, copyCap]
  omega

theorem emitProjectionCell_exec {q : ℕ} (G : Instance q) (p u v a : ℕ)
    (hp : 0 < p) (ha : a < 4*q) (out : List Bool) :
    ∃ t, emitProjectionCell.Exec (emitterStore G p u v a out)
      (emitterStore G p u v a (unary true false (projectionIndex G p u v a) ++ out)) t ∧
      t ≤ projectionEmitterBound (recordBits G).length G.edges.length q p u v a := by
  let parent := emitterParent G p u v a out
  let word := unary true false (projectionIndex G p u v a)
  let endBank := Fin.append (decodedCell G p u v a (word ++ [])) (fun _ : Fin 3 => [])
  obtain ⟨t, ht, hb⟩ := projectionAtom_exec G p u v a hp ha []
  have hbody := appendLeft_exec ht (fun _ : Fin 3 => [])
  rw [← loadedProjection G p u v a out] at hbody
  have hword : endBank 23 = word := by
    change word ++ [] = word
    simp
  obtain ⟨c, hc, hcb⟩ := callBank_exec parent 19 15 23 projectionInputs projectionInBank
    endBank word t _ rfl (by decide) (by simp [projectionInputs]) hbody hword hb
  rw [show parent 15 = out from rfl, updateOutput] at hc
  refine ⟨c,hc,?_⟩
  have hcst : copyCost parent projectionInputs ≤
      9*(6*copyCap (recordBits G).length G.edges.length q p u v a+4)+1 :=
    copyCost_le parent projectionInputs _ (fun sd hs =>
      operandsBound G p u v a out sd.1 (List.mem_map.mpr ⟨sd,hs,rfl⟩))
  unfold projectionEmitterBound
  omega

theorem emitAdjacencyCell_exec {q : ℕ} (G : Instance q) (p u v : ℕ) (hp : 0 < p) (out : List Bool) :
    ∃ t, emitAdjacencyCell.Exec (emitterStore G p u v 0 out)
      (emitterStore G p u v 0 (edgeBit G p u v :: out)) t ∧
      t ≤ adjacencyEmitterBound (recordBits G).length G.edges.length q p u v
        (G.leftVertices+G.rightVertices) := by
  let parent := emitterParent G p u v 0 out
  let word := [edgeBit G p u v]
  let endBank := adjacencyDecoded G p u v word
  obtain ⟨t, ht, hb⟩ := adjacencyAtom_exec G p u v hp []
  rw [← loadedAdjacency G p u v out] at ht
  obtain ⟨c, hc, hcb⟩ := callBank_exec parent 19 15 35 adjacencyInputs adjacencyAtom
    endBank word t _ rfl (by decide) (by simp [adjacencyInputs]) ht rfl hb
  rw [show parent 15 = out from rfl, updateOutput] at hc
  refine ⟨c,hc,?_⟩
  have hin : ∀ i ∈ adjacencyInputs.map Prod.fst, i ∈ projectionInputs.map Prod.fst := by
    simp [adjacencyInputs, projectionInputs]
  have hcst : copyCost parent adjacencyInputs ≤
      7*(6*copyCap (recordBits G).length G.edges.length q p u v 0+4)+1 :=
    copyCost_le parent adjacencyInputs _ (fun sd hs =>
      operandsBound G p u v 0 out sd.1 (hin _ (List.mem_map.mpr ⟨sd,hs,rfl⟩)))
  unfold adjacencyEmitterBound
  omega

end FourToOneGames.WordMachines.LiftOutput

end

/- LiftRuntimeBounds -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.LiftOutput

open OAI.PerfectCompleteness LiftInput Radix

def cellTime (cap : ℕ) : ℕ := 100000*(cap+1)^3

theorem projectionTime_le {n count q p u v a cap : ℕ}
    (hn : n ≤ cap) (hm : count ≤ cap) (hq : q ≤ cap) (hp : p ≤ cap)
    (hu : u ≤ cap) (hv : v ≤ cap) (ha : a ≤ cap) :
    projectionEmitterBound n count q p u v a ≤ cellTime cap := by
  have hmono : projectionEmitterBound n count q p u v a ≤
      projectionEmitterBound cap cap cap cap cap cap cap := by
    unfold projectionEmitterBound copyCap projectionAtomBound projectionValueBound tagBound
      extractBound RecordLookup.guardedBound RecordLookup.stepBound
    dsimp only
    gcongr
  apply hmono.trans
  unfold projectionEmitterBound copyCap projectionAtomBound projectionValueBound tagBound
    extractBound RecordLookup.guardedBound RecordLookup.stepBound cellTime
  dsimp only
  ring_nf
  omega

theorem adjacencyTime_le {n count q p u v sizes cap : ℕ}
    (hn : n ≤ cap) (hm : count ≤ cap) (hq : q ≤ cap) (hp : p ≤ cap)
    (hu : u ≤ cap) (hv : v ≤ cap) (hs : sizes ≤ cap) :
    adjacencyEmitterBound n count q p u v sizes ≤ cellTime cap := by
  have hmono : adjacencyEmitterBound n count q p u v sizes ≤
      adjacencyEmitterBound cap cap cap cap cap cap cap := by
    unfold adjacencyEmitterBound copyCap adjacencyAtomBound adjacencyValueBound tagBound
      extractBound RecordLookup.guardedBound RecordLookup.stepBound
    dsimp only
    gcongr
  apply hmono.trans
  unfold adjacencyEmitterBound copyCap adjacencyAtomBound adjacencyValueBound tagBound
    extractBound RecordLookup.guardedBound RecordLookup.stepBound cellTime
  dsimp only
  ring_nf
  omega

def traversalCap (B len : ℕ) : ℕ :=
  let primeCap := 2*(len+B)
  len*(primeCap+1)^4 + primeCap + 8*len + 2

theorem traversalCap_ge {q : ℕ} (G : Instance q) (B : ℕ) (hB : 0 < B) :
    let len := (Encoding.gameBits G).length
    let p := choosePrime B G.edges.length hB
    let cap := traversalCap B len
    p ≤ cap ∧ G.leftVertices*p^3 ≤ cap ∧ G.rightVertices*p^4 ≤ cap ∧ 4*q ≤ cap ∧
      (recordBits G).length ≤ cap ∧ G.edges.length ≤ cap ∧ q ≤ cap ∧
      G.leftVertices+G.rightVertices ≤ cap := by
  let len := (Encoding.gameBits G).length
  let p := choosePrime B G.edges.length hB
  let b := 2*(len+B)
  obtain ⟨hp, hl, hr, hq⟩ := liftSizeBounds G B hB
  change p ≤ b at hp
  change G.leftVertices*p^3 ≤ len*b^3 at hl
  change G.rightVertices*p^4 ≤ len*b^4 at hr
  have h3 : b^3 ≤ (b+1)^4 :=
    (Nat.pow_le_pow_left (Nat.le_succ b) 3).trans
      (Nat.pow_le_pow_right (Nat.succ_pos b) (by decide))
  have h4 : b^4 ≤ (b+1)^4 := Nat.pow_le_pow_left (Nat.le_succ b) 4
  have hl' := hl.trans (Nat.mul_le_mul_left len h3)
  have hr' := hr.trans (Nat.mul_le_mul_left len h4)
  have hh := headerLength_le G
  have hw := recordBits_length_le G
  dsimp only
  change p ≤ len*(b+1)^4+b+8*len+2 ∧
      G.leftVertices*p^3 ≤ len*(b+1)^4+b+8*len+2 ∧
      G.rightVertices*p^4 ≤ len*(b+1)^4+b+8*len+2 ∧
      4*q ≤ len*(b+1)^4+b+8*len+2 ∧
      (recordBits G).length ≤ len*(b+1)^4+b+8*len+2 ∧
      G.edges.length ≤ len*(b+1)^4+b+8*len+2 ∧
      q ≤ len*(b+1)^4+b+8*len+2 ∧
      G.leftVertices+G.rightVertices ≤ len*(b+1)^4+b+8*len+2
  change G.leftVertices+G.rightVertices+q+G.edges.length+4 ≤ len at hh
  change (recordBits G).length ≤ len at hw
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

open Polynomial in
noncomputable def liftBudget (B : ℕ) : Polynomial ℕ :=
  let p := 2*(X+C B)
  let cap := X*(p+1)^4 + p + 8*X + 2
  let entry := 100000*(cap+1)^3
  prepareBudget B + (12*X+15) +
    (cap*(cap*(cap*(entry+4)+6*cap+9)+6*cap+9)+6*cap+5) +
    (cap*(cap*(entry+4)+6*cap+9)+6*cap+5) + headerBudget B + 4

theorem liftBudget_eval (B len : ℕ) :
    let cap := traversalCap B len
    let entry := cellTime cap
    (liftBudget B).eval len =
      (prepareBudget B).eval len + (12*len+15) +
        (cap*(cap*(cap*(entry+4)+6*cap+9)+6*cap+9)+6*cap+5) +
        (cap*(cap*(entry+4)+6*cap+9)+6*cap+5) + (headerBudget B).eval len + 4 := by
  simp [liftBudget, traversalCap, cellTime]

end FourToOneGames.WordMachines.LiftOutput

end

/- LiftAssembly -/
section

set_option autoImplicit false

namespace FourToOneGames.WordMachines.LiftOutput

open CookPvsNP OAI.PerfectCompleteness LiftInput BankCalls

private def rectanglePorts : Fin 5 ↪ Fin 62 := ⟨![16,17,15,11,19], by decide⟩
private def projectionPorts : Fin 8 ↪ Fin 62 := ⟨![16,17,15,11,19,18,12,20], by decide⟩

private def counters (u v a width two : ℕ) : Fin 7 → List Bool :=
  ![List.replicate u true,List.replicate v true,List.replicate a true,[],[],
    List.replicate width true,List.replicate two true]

private def addConstants : StackProg (Fin 7) Bool :=
  .seq (pushProg 5 true) (.seq (pushProg 5 true) (.seq (pushProg 6 true) (pushProg 6 true)))

private noncomputable def initializeConstants : StackProg (Fin 23) Bool :=
  .seq (copyProg 3 21 19) (.seq (copyProg 3 21 19) (onPorts (Fin.natAddEmb 16) addConstants))

private def refillRow : StackProg (Fin 23) Bool := copyProg 10 16 19

noncomputable def projectionPass : StackProg (Fin 62) Bool :=
  .seq (onPorts (Fin.castAddEmb 39) refillRow) (emitProjectionTable projectionPorts emitProjectionCell)

noncomputable def adjacencyPass : StackProg (Fin 62) Bool :=
  .seq (onPorts (Fin.castAddEmb 39) refillRow) (emitRectangle rectanglePorts emitAdjacencyCell)

noncomputable def liftedMachine (B : ℕ) : StackProg (Fin 62) Bool :=
  .seq (onPorts (Fin.castAddEmb 39) (onPorts (Fin.castAddEmb 7) (prepareOutput B)))
    (.seq (onPorts (Fin.castAddEmb 39) initializeConstants)
      (.seq projectionPass (.seq adjacencyPass
        (onPorts (Fin.castAddEmb 39) (onPorts (Fin.castAddEmb 7) writeHeader)))))

private theorem addConstants_exec (width : ℕ) :
    addConstants.Exec (counters 0 0 0 width 0) (counters 0 0 0 (width+2) 2) 7 := by
  have hstep (n d : ℕ) :
      (pushProg (5 : Fin 7) true).Exec (counters 0 0 0 n d) (counters 0 0 0 (n+1) d) 1 := by
    convert pushBit_exec (5 : Fin 7) true (counters 0 0 0 n d) using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  have hTwo (n d : ℕ) :
      (pushProg (6 : Fin 7) true).Exec (counters 0 0 0 n d) (counters 0 0 0 n (d+1)) 1 := by
    convert pushBit_exec (6 : Fin 7) true (counters 0 0 0 n d) using 1
    exact funext (fun k => by fin_cases k <;> rfl)
  exact (hstep width 0).seq ((hstep (width+1) 0).seq ((hTwo (width+2) 0).seq (hTwo (width+2) 1)))

theorem initializeConstants_exec {q : ℕ} (G : Instance q) (p : ℕ) (out : List Bool) :
    initializeConstants.Exec
      (Fin.append (withOutput (dimensionStore G p) out) (fun _ : Fin 7 => []))
      (emitterParent G p 0 0 0 out) (12*q+15) := by
  let header := withOutput (dimensionStore G p) out
  have hcopy (n : ℕ) :
      (copyProg (3 : Fin 23) 21 19).Exec (Fin.append header (counters 0 0 0 n 0))
        (Fin.append header (counters 0 0 0 (q+n) 0)) (6*q+3) := by
    have h := copyAppendRight_exec header (counters 0 0 0 n 0) 3 5 3 (by decide) rfl
    have hs : header 3 = List.replicate q true := rfl
    have hdst : counters 0 0 0 n 0 5 = List.replicate n true := rfl
    have hup : Function.update (counters 0 0 0 n 0) 5 (List.replicate (q+n) true) =
        counters 0 0 0 (q+n) 0 := by
      funext k
      fin_cases k <;> rfl
    rw [hs, hdst, List.length_replicate, ← List.replicate_add, hup] at h
    exact h
  have hr := (hcopy 0).seq ((hcopy q).seq (appendRight_exec (addConstants_exec (q+q)) header))
  have hw : (q+q)+2 = 2+2*q := by omega
  have hzero : counters 0 0 0 0 0 = fun _ => [] := by
    funext i
    fin_cases i <;> rfl
  rw [hw, hzero] at hr
  convert hr using 1 <;> first | rfl | omega

private theorem refillRow_exec {q : ℕ} (G : Instance q) (p : ℕ) (out : List Bool) :
    (onPorts (Fin.castAddEmb 39) refillRow).Exec (emitterStore G p 0 0 0 out)
      (emitterStore G p (G.leftVertices*p^3) 0 0 out) (6*(G.leftVertices*p^3)+3) := by
  let header := withOutput (dimensionStore G p) out
  let regs := counters 0 0 0 (2+2*q) 2
  have hr := copyAppendRight_exec header regs 10 0 3 (by decide) rfl
  have hsrc : header 10 = List.replicate (G.leftVertices*p^3) true := rfl
  have hdst : regs 0 = [] := rfl
  have heq : Function.update regs 0 (List.replicate (G.leftVertices*p^3) true) =
      counters (G.leftVertices*p^3) 0 0 (2+2*q) 2 := by
    funext k
    fin_cases k <;> rfl
  rw [hsrc, hdst, List.append_nil, List.length_replicate, heq] at hr
  exact appendLeft_exec hr (fun _ : Fin 39 => [])

private theorem projectionFrame_eq {q : ℕ} (G : Instance q) (p u v a : ℕ) (out : List Bool) :
    projectionFrame projectionPorts (emitterStore G p 0 0 0 []) true u v a out =
      emitterStore G p u v a out := by
  change Function.update (Function.update (Function.update (Function.update
    (emitterStore G p 0 0 0 []) ((16 : Fin 23).castAdd 39) (List.replicate u true))
    ((17 : Fin 23).castAdd 39) (List.replicate v true))
    ((18 : Fin 23).castAdd 39) (List.replicate a true))
    ((15 : Fin 23).castAdd 39) out = _
  simp only [emitterStore, append_update_left (n := 23) (m := 39)]
  apply congrArg (fun s : Fin 23 → List Bool => Fin.append s (fun _ : Fin 39 => []))
  change Function.update (Function.update (Function.update (Function.update
    (Fin.append (withOutput (dimensionStore G p) []) (counters 0 0 0 (2+2*q) 2))
    ((0 : Fin 7).natAdd 16) (List.replicate u true))
    ((1 : Fin 7).natAdd 16) (List.replicate v true))
    ((2 : Fin 7).natAdd 16) (List.replicate a true))
    ((15 : Fin 16).castAdd 7) out =
    Fin.append (withOutput (dimensionStore G p) out) (counters u v a (2+2*q) 2)
  simp only [append_update_left (n := 16) (m := 7), append_update_right (n := 16) (m := 7),
    withOutput_update]
  apply congrArg (Fin.append (withOutput (dimensionStore G p) out))
  funext k
  fin_cases k <;> rfl

private theorem rectangleFrame_eq {q : ℕ} (G : Instance q) (p u v : ℕ) (out : List Bool) :
    rectangleFrame rectanglePorts (emitterStore G p 0 0 0 []) true u v out =
      emitterStore G p u v 0 out := by
  let uv := Function.update (Function.update (emitterStore G p 0 0 0 [])
    16 (List.replicate u true)) 17 (List.replicate v true)
  have hzero : Function.update uv 18 [] = uv := Function.update_eq_self _ _
  have h := projectionFrame_eq G p u v 0 out
  change Function.update (Function.update uv 18 []) 15 out = _ at h
  rw [hzero] at h
  exact h

def projectionWordsFor {q : ℕ} (G : Instance q) (p : ℕ) : List Bool :=
  rectangleWords (fun u v => ascendingWords (fun a => unary true false (projectionIndex G p u v a))
    (4*q)) (G.leftVertices*p^3) (G.rightVertices*p^4)

def adjacencyWordsFor {q : ℕ} (G : Instance q) (p : ℕ) : List Bool :=
  rectangleWords (fun u v => [edgeBit G p u v]) (G.leftVertices*p^3) (G.rightVertices*p^4)

theorem projectionPass_exec {q : ℕ} (G : Instance q) (p budget : ℕ) (hp : 0 < p)
    (hbudget : ∀ u < G.leftVertices*p^3, ∀ v < G.rightVertices*p^4, ∀ a < 4*q,
      projectionEmitterBound (recordBits G).length G.edges.length q p u v a ≤ budget)
    (out : List Bool) :
    ∃ t, projectionPass.Exec (emitterStore G p 0 0 0 out)
      (emitterStore G p 0 0 0 (projectionWordsFor G p ++ out)) t ∧
      t ≤ (G.leftVertices*p^3) * ((G.rightVertices*p^4) *
        ((4*q)*(budget+4)+6*(4*q)+9) + 6*(G.rightVertices*p^4)+9) +
        6*(G.leftVertices*p^3)+5 := by
  obtain ⟨t, ht, hb⟩ := emitProjectionTable_exec projectionPorts (emitterStore G p 0 0 0 []) true
    (G.leftVertices*p^3) (G.rightVertices*p^4) (4*q) emitProjectionCell
    (fun u v a => unary true false (projectionIndex G p u v a)) budget out rfl rfl rfl rfl
    (fun i hi j hj a ha tail => by
      obtain ⟨s, hs, hsb⟩ := emitProjectionCell_exec G p i j a hp ha tail
      refine ⟨s, ?_, hsb.trans (hbudget i hi j hj a ha)⟩
      simpa only [projectionFrame_eq] using hs)
  rw [projectionFrame_eq, projectionFrame_eq] at ht
  exact ⟨_, (refillRow_exec G p out).seq ht, by omega⟩

theorem adjacencyPass_exec {q : ℕ} (G : Instance q) (p budget : ℕ) (hp : 0 < p)
    (hbudget : ∀ u < G.leftVertices*p^3, ∀ v < G.rightVertices*p^4,
      adjacencyEmitterBound (recordBits G).length G.edges.length q p u v
        (G.leftVertices+G.rightVertices) ≤ budget)
    (out : List Bool) :
    ∃ t, adjacencyPass.Exec (emitterStore G p 0 0 0 out)
      (emitterStore G p 0 0 0 (adjacencyWordsFor G p ++ out)) t ∧
      t ≤ (G.leftVertices*p^3) * ((G.rightVertices*p^4)*(budget+4) +
        6*(G.rightVertices*p^4)+9) + 6*(G.leftVertices*p^3)+5 := by
  obtain ⟨t, ht, hb⟩ := emitRectangle_exec rectanglePorts (emitterStore G p 0 0 0 []) true
    (G.leftVertices*p^3) (G.rightVertices*p^4) emitAdjacencyCell
    (fun u v => [edgeBit G p u v]) budget out rfl rfl
    (fun i hi j hj tail => by
      obtain ⟨s, hs, hsb⟩ := emitAdjacencyCell_exec G p i j hp tail
      exact ⟨s, by simpa only [rectangleFrame_eq, List.singleton_append] using hs, hsb.trans (hbudget i hi j hj)⟩)
  rw [rectangleFrame_eq, rectangleFrame_eq] at ht
  exact ⟨_, (refillRow_exec G p out).seq ht, by omega⟩

private theorem initAppend {n m : ℕ} (P : StackProg (Fin (n+m)) Bool)
    (Q : StackProg (Fin n) Bool) (k : Fin n) (w : List Bool) :
    (P.machine.init (k.castAdd m) w).store =
      Fin.append (Q.machine.init k w).store (fun _ : Fin m => []) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · by_cases hi : i = k
    · subst i
      simp [StackMachine.init]
    · have hne : i.castAdd m ≠ k.castAdd m :=
        fun he => hi (Fin.ext (congrArg (fun a : Fin (n+m) => a.val) he))
      simp [StackMachine.init, hi, hne]
  · have hne : i.natAdd n ≠ k.castAdd m := by
      intro he
      have hv : n+i.val = k.val := congrArg Fin.val he
      omega
    simp [StackMachine.init, hne]

/-- The complete lift transducer, from the published 2-to-1 input to the lifted LabelCover word. -/
noncomputable def liftOutputTM (q : ℕ) (hq : 0 < q) (B : ℕ) (hB : 0 < B) :
    Turing.TM2ComputableInPolyTime (Encoding.gameBits (q := q)) encodeLabelCover (liftOutput hq B hB) :=
  StackTM2Time.programPolytime Encoding.gameBits encodeLabelCover (liftOutput hq B hB)
    (liftedMachine B) 0 15 (liftBudget B) (fun G => by
      let len := (Encoding.gameBits G).length
      let p := choosePrime B G.edges.length hB
      let cap := traversalCap B len
      let entry := cellTime cap
      let pr := projectionWordsFor G p
      let ad := adjacencyWordsFor G p
      let word := outputHeader G p ++ (ad ++ pr)
      have hp : p.Prime := (choosePrime_spec B G.edges.length hB).1
      let primeFact : Fact p.Prime := ⟨hp⟩
      have hcount : G.edges.length ≤ p :=
        (Nat.le_max_left G.edges.length B).trans (choosePrime_spec B G.edges.length hB).2.1.le
      have hword : encodeLabelCover (liftOutput hq B hB G) = word := by
        change encodeLabelCover (SimpleLift.game (p := p) G hq hcount) = word
        simpa only [word, outputHeader, ad, pr, adjacencyWordsFor, projectionWordsFor, List.append_assoc]
          using liftedEncoding_words (p := p) G hq hcount
      obtain ⟨hpc, hL, hR, hA, hrecord, hm, hqc, hsv⟩ := traversalCap_ge G B hB
      obtain ⟨s, hs, hsb⟩ := prepareOutput_exec G B hB
      have hprep := appendLeft_exec (appendLeft_exec hs (fun _ : Fin 7 => [])) (fun _ : Fin 39 => [])
      have hinit : ((liftedMachine B).machine.init 0 (Encoding.gameBits G)).store =
          Fin.append (Fin.append (((prepareOutput B).machine.init 0 (Encoding.gameBits G)).store)
            (fun _ : Fin 7 => [])) (fun _ : Fin 39 => []) := by
        let inner := onPorts (Fin.castAddEmb 7) (prepareOutput B)
        have h1 : ((liftedMachine B).machine.init 0 (Encoding.gameBits G)).store =
            Fin.append (inner.machine.init 0 (Encoding.gameBits G)).store (fun _ : Fin 39 => []) :=
          initAppend (n := 23) (m := 39) (liftedMachine B) inner 0 (Encoding.gameBits G)
        have h2 : (inner.machine.init 0 (Encoding.gameBits G)).store =
            Fin.append (((prepareOutput B).machine.init 0 (Encoding.gameBits G)).store)
              (fun _ : Fin 7 => []) :=
          initAppend (n := 16) (m := 7) inner (prepareOutput B) 0 (Encoding.gameBits G)
        exact h1.trans (congrArg (fun f : Fin 23 → List Bool => Fin.append f (fun _ : Fin 39 => [])) h2)
      rw [← hinit] at hprep
      have hconst := appendLeft_exec (initializeConstants_exec G p []) (fun _ : Fin 39 => [])
      obtain ⟨t, ht, htb⟩ := projectionPass_exec G p entry hp.pos
        (fun u hu v hv a ha => projectionTime_le hrecord hm hqc hpc
          (hu.le.trans hL) (hv.le.trans hR) (ha.le.trans hA)) []
      rw [List.append_nil] at ht
      obtain ⟨u, hu, hub⟩ := adjacencyPass_exec G p entry hp.pos
        (fun i hi j hj => adjacencyTime_le hrecord hm hqc hpc
          (hi.le.trans hL) (hj.le.trans hR) hsv) pr
      have hheader := appendLeft_exec (appendLeft_exec (writeHeader_exec G p (ad ++ pr))
        (counters 0 0 0 (2+2*q) 2)) (fun _ : Fin 39 => [])
      have hrun := hprep.seq (hconst.seq (ht.seq (hu.seq hheader)))
      refine ⟨emitterStore G p 0 0 0 word, _, hrun, ?_, ?_⟩
      · change word = _
        exact hword.symm
      · have hsized := headerLength_le G
        have hh := headerBudget_ge G B hB
        dsimp only at hh
        have ht' : t ≤ cap*(cap*(cap*(entry+4)+6*cap+9)+6*cap+9)+6*cap+5 :=
          htb.trans (by gcongr)
        have hu' : u ≤ cap*(cap*(entry+4)+6*cap+9)+6*cap+5 :=
          hub.trans (by gcongr)
        change _ ≤ (liftBudget B).eval len
        rw [liftBudget_eval]
        change _ ≤ (prepareBudget B).eval len + (12*len+15) +
          (cap*(cap*(cap*(entry+4)+6*cap+9)+6*cap+9)+6*cap+5) +
          (cap*(cap*(entry+4)+6*cap+9)+6*cap+5) + (headerBudget B).eval len + 4
        change s ≤ (prepareBudget B).eval len at hsb
        change G.leftVertices+G.rightVertices+q+G.edges.length+4 ≤ len at hsized
        change 6*(G.leftVertices*p^3+G.rightVertices*p^4+5*q)+23 ≤ (headerBudget B).eval len at hh
        omega)

end FourToOneGames.WordMachines.LiftOutput

namespace FourToOneGames

open Turing OAI.PerfectCompleteness

/-- Compile 2-to-1 instances into simple 4-to-1 games with arbitrarily small additive loss. -/
theorem simple_four_to_one_lift : SimpleFourToOneLift :=
  simpleFourToOneLift_of_machine_certificate
    (fun q hq B hB => ⟨WordMachines.LiftOutput.liftOutputTM q hq B hB⟩)

/-- Apply the verified lift to a certificate for the source SAT compiler. -/
theorem four_to_one_perfect_completeness_of_sat_certificate
    (twoToOne : ∀ δ : ℚ, 0 < δ → δ < 1 → Nonempty (BinaryGapReduction δ))
    (satTM : Nonempty (TM2ComputableInPolyTime encodeLabelCover (id : List Bool → List Bool) binaryInput)) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ r₀ : ℕ, ∃ r : ℕ,
      Nonempty (GapReduction encodeLabelCover encodeLabelCover
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val = 1)
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val ≤ s)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val = 1)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val ≤ ε)) :=
  four_to_one_perfect_completeness_of_compilers twoToOne
    (fun _ => ⟨binaryInput, satTM, fun P _ => binaryInput_spec P⟩)
    simple_four_to_one_lift

end FourToOneGames

end

/- SATCertificate -/
section

set_option autoImplicit false
set_option Elab.async false

namespace FourToOneGames.SATMachine

open ProjSchedTW.Complexity Turing
open WordMachines.UnaryPair
open Polynomial

/-- The word-level running-time bound as a polynomial in the input length. -/
private noncomputable def satBudget (C : ℕ) : Polynomial ℕ :=
  let cap : Polynomial ℕ := X+1
  let name := 4*cap + (4*cap+(4*cap+1)^2+1)^2
  let numeral := (name+1)^2
  let pair := (6*name+13)*name+30*name+50
  let pairPass := 10*(6*name+9)+10*pair+7
  let numeralPass := 3*pairPass+6*name+Polynomial.C C*(numeral+1)^2+3*numeral+11
  let literal := 10*(4*(6*cap+4)+1)+10*numeralPass+7
  let clause := 3*(literal+1)+3
  let transition := 3*(literal+1)+10*cap+24
  let vertex := cap*(transition+4)+6*cap+2*clause+7
  let vertices := cap*(vertex+4)+1
  let compare := 3*(literal+1)+24*cap+30
  let labels := cap*(compare+4)+6*cap+5
  let indexes := (6*cap+13)*cap+(6*(cap+1)^2+13)*cap+12*cap+30
  let table := fun (time : Polynomial ℕ) => 10*(6*(cap+cap)+9)+10*time+7
  let prepare := indexes+table (15*cap+11)+table (20*cap+15)+2
  let cell := prepare+labels+3*cap+5
  let constraints := cap*(cap*(cap*(cell+4)+6*cap+9)+6*cap+9)+1
  let pass := fun (b : Polynomial ℕ) => 10*(7*(6*cap+4)+1)+10*b+7
  let full := pass constraints+2*pass vertices+2
  30*cap+60+full+2*Polynomial.C emptyGameWord.length+1

private theorem satBudget_eval (C len : ℕ) : (satBudget C).eval len = satProgramTime C len := by
  simp only [satBudget, satProgramTime, satNonemptyBound, satPassBound, constraintTableBound,
    edgeCellBound, prepareEdgeCellBound, queryTableBound, denseIndicesBound, conflictLabelsBound,
    conflictTrialBound, vertexSideBound, vertexChoicesBound, choiceTransitionBound, choiceUnitBound,
    literalCallBound, namedLiteralBound, variableNameCap, pairPassBound, pairBound,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]

def nativeEncoding (P : LabelCover) : List BSym := (encodeLabelCover P).map nativeBit

private noncomputable def nativeEncodingTM :
    TM2ComputableInPolyTime encodeLabelCover nativeEncoding (id : LabelCover → LabelCover) where
  tm := nativeBits_polytime.tm
  inputAlphabet := nativeBits_polytime.inputAlphabet
  outputAlphabet := nativeBits_polytime.outputAlphabet
  time := nativeBits_polytime.time
  outputsFun P := nativeBits_polytime.outputsFun (encodeLabelCover P)

local instance : Inhabited BSym := ⟨.zero⟩

private noncomputable def nativeSATTM (writer : CookPvsNP.StackProg (Fin 5) BSym) (C : ℕ)
    (hw : IsNumeralWriter writer C) :
    TM2ComputableInPolyTime nativeEncoding formulaWord satFormula :=
  StackTM2Time.programPolytime nativeEncoding formulaWord satFormula (satProgram writer) 0 10
    (satBudget C) (fun P => by
      obtain ⟨t, ht, hb⟩ := satProgram_exec writer C hw P
      exact ⟨_, t, ht, rfl, by simpa only [satBudget_eval, nativeEncoding] using hb⟩)

theorem satFormulaTM : Nonempty (TM2ComputableInPolyTime encodeLabelCover formulaWord satFormula) := by
  obtain ⟨writer, C, hw⟩ := exists_numeralWriter
  exact Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch (g := satFormula)
    nativeEncodingTM (nativeSATTM writer C hw)

/-- The end-to-end certificate for the source-game to binary 3SAT transformation. -/
theorem binaryInputTM :
    Nonempty (TM2ComputableInPolyTime encodeLabelCover (id : List Bool → List Bool) binaryInput) := by
  obtain ⟨h⟩ := satFormulaTM
  exact binaryInput_polytime_of_formula h

end FourToOneGames.SATMachine

namespace FourToOneGames

open OAI.PerfectCompleteness

/-- Assemble the two certified transducers around the binary 3SAT to 2-to-1 reduction. -/
theorem four_to_one_perfect_completeness_of_two_to_one
    (twoToOne : ∀ δ : ℚ, 0 < δ → δ < 1 → Nonempty (BinaryGapReduction δ)) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ r₀ : ℕ, ∃ r : ℕ,
      Nonempty (GapReduction encodeLabelCover encodeLabelCover
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val = 1)
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val ≤ s)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val = 1)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val ≤ ε)) :=
  four_to_one_perfect_completeness_of_machine_certificates twoToOne SATMachine.binaryInputTM
    (fun q hq B hB => ⟨WordMachines.LiftOutput.liftOutputTM q hq B hB⟩)

end FourToOneGames

end

open FourToOneGames in
theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ r₀ : ℕ, ∃ r : ℕ,
      Nonempty (GapReduction encodeLabelCover encodeLabelCover
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val = 1)
        (fun P : LabelCover => LabelCover.AlphabetBound r₀ P ∧ P.val ≤ s)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val = 1)
        (fun Q : LabelCover =>
          LabelCover.AlphabetBound r Q ∧ LabelCover.IsDToOne 4 Q ∧ Q.val ≤ ε)) :=
  FourToOneGames.four_to_one_perfect_completeness_of_two_to_one
    OAI.PerfectCompleteness.Theorem11.exists_reduction
