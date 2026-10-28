-- Prove2me | solution 1 for BitcoinVerify.parseScript_pushes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:42:28.150635+00:00
-- url     : https://prove2.me/submissions/0250a8e0-4be5-4611-8784-a57a5c8395c7

import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
theorem S189B_leLen (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem S189B_leVal2 (n : Nat) (h : n < 65536) : leVal (leBytes 2 n) = n := by
  simp [leBytes, leVal, BitVec.toNat_ofNat]; omega

theorem S189B_tn (k : Nat) (h : k < 256) : (BitVec.ofNat 8 k).toNat = k := by
  simp [BitVec.toNat_ofNat]; omega

theorem S189B_getOp_push (d r : Bytes) (hd : d.length ≤ 520) :
    getOp (pushBytes d ++ r) = some (.push d, r) := by
  unfold pushBytes
  by_cases h1 : d.length < OP_PUSHDATA1
  · simp only [h1, if_true, List.cons_append]
    simp only [OP_PUSHDATA1] at h1
    simp [getOp, S189B_tn _ (show d.length < 256 by omega), OP_PUSHDATA4, OP_PUSHDATA1, h1,
      show d.length ≤ 78 by omega]
  · by_cases h2 : d.length ≤ 0xff
    · simp only [h1, h2, if_true, if_false, List.cons_append, List.append_assoc]
      simp only [OP_PUSHDATA1] at h1
      simp [getOp, S189B_tn _ (show d.length < 256 by omega), OP_PUSHDATA4, OP_PUSHDATA1]
    · have h3 : d.length ≤ 0xffff := by omega
      simp only [h1, h2, h3, if_true, if_false, List.cons_append, List.append_assoc]
      simp only [OP_PUSHDATA1] at h1
      simp [getOp, OP_PUSHDATA4, OP_PUSHDATA1, OP_PUSHDATA2, S189B_leLen,
        S189B_leVal2 _ (show d.length < 65536 by omega)]
      rw [if_neg (by omega)]; simp

theorem S189B_pb_len (d : Bytes) : d.length + 1 ≤ (pushBytes d).length := by
  unfold pushBytes; repeat' split
  all_goals simp [S189B_leLen]

theorem S189B_parse_cons (f : Nat) (s : Bytes) (hs : s ≠ []) :
    parseScriptAux (f + 1) s = match getOp s with
      | none => none
      | some (i, r) => match parseScriptAux f r with
        | none => none
        | some is => some (i :: is) := by
  cases s with
  | nil => exact absurd rfl hs
  | cons a t => rfl

theorem S189B_po_cons (f : Nat) (s : Bytes) (hs : s ≠ []) :
    isPushOnlyAux (f + 1) s = match getOp s with
      | none => false
      | some (.push _, r) => isPushOnlyAux f r
      | some (.op c, r) => if BitcoinScript.OP_16 < c then false else isPushOnlyAux f r := by
  cases s with
  | nil => exact absurd rfl hs
  | cons a t => rfl

theorem S189B_ne (d r : Bytes) : pushBytes d ++ r ≠ [] := by
  intro h
  have h1 := congrArg List.length h
  simp only [List.length_append, List.length_nil] at h1
  have := S189B_pb_len d
  omega

theorem S189B_parse_aux (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ 520) :
    ∀ f, (pushesBytes ps).length ≤ f → parseScriptAux f (pushesBytes ps) = some (ps.map Instr.push) := by
  induction ps with
  | nil => intro f _; cases f <;> rfl
  | cons p ps ih =>
    intro f hf
    have e : pushesBytes (p :: ps) = pushBytes p ++ pushesBytes ps := by simp [pushesBytes]
    rw [e] at hf ⊢
    have hl := S189B_pb_len p
    simp only [List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [S189B_parse_cons _ _ (S189B_ne _ _), S189B_getOp_push _ _ (hp p (by simp))]
    simp only
    rw [ih (fun q hq => hp q (by simp [hq])) g (by omega)]
    rfl

theorem S189B_po_aux (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ 520) :
    ∀ f, (pushesBytes ps).length ≤ f → isPushOnlyAux f (pushesBytes ps) = true := by
  induction ps with
  | nil => intro f _; cases f <;> rfl
  | cons p ps ih =>
    intro f hf
    have e : pushesBytes (p :: ps) = pushBytes p ++ pushesBytes ps := by simp [pushesBytes]
    rw [e] at hf ⊢
    have hl := S189B_pb_len p
    simp only [List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [S189B_po_cons _ _ (S189B_ne _ _), S189B_getOp_push _ _ (hp p (by simp))]
    exact ih (fun q hq => hp q (by simp [hq])) g (by omega)

theorem S189B_parse_pushes (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinSig.parseScript (BitcoinVerify.pushesBytes ps) = some (ps.map Instr.push) :=
  S189B_parse_aux ps hp _ (Nat.le_refl _)

theorem S189B_po_pushes (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.isPushOnly (BitcoinVerify.pushesBytes ps) = true :=
  S189B_po_aux ps hp _ (Nat.le_refl _)

open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
theorem solution (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinSig.parseScript (BitcoinVerify.pushesBytes ps) = some (ps.map Instr.push) := by
  exact S189B_parse_pushes ps hp
