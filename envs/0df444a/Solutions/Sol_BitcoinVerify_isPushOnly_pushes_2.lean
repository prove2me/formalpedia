-- Prove2me | solution 2 for BitcoinVerify.isPushOnly_pushes
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:56.670547+00:00
-- url     : https://prove2.me/submissions/4e361125-5d52-4c36-a6ec-48f121e18239

import Definitions.Def_BitcoinVerify
import Theorems.Thm_BitcoinSig_parseScript_p2pkh
import Theorems.Thm_BitcoinScript_eval_pushes
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinSer_hash160_length

open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

private theorem getD_app_lt {α : Type} (a b : List α) (i : Nat) (d : α) (h : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_app_ge {α : Type} (a b : List α) (i : Nat) (d : α) (h : a.length ≤ i) :
    (a ++ b).getD i d = b.getD (i - a.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem ofNat_toNat' (b : Byte) : BitVec.ofNat 8 b.toNat = b := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem pushBytes_short (d : Bytes) (hd : d.length < 76) : pushBytes d = BitVec.ofNat 8 d.length :: d := by
  unfold pushBytes OP_PUSHDATA1; rw [if_pos hd]

private theorem leBytes_len (k n : Nat) : (BitcoinSer.leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [BitcoinSer.leBytes, ih]

private theorem leVal_leBytes2 (n : Nat) (h : n < 65536) : BitcoinSer.leVal (BitcoinSer.leBytes 2 n) = n := by
  simp [BitcoinSer.leBytes, BitcoinSer.leVal, BitVec.toNat_ofNat]; omega

private theorem getOp_pushBytes (d rest : Bytes) (hd : d.length ≤ MAX_SCRIPT_ELEMENT_SIZE) :
    getOp (pushBytes d ++ rest) = some (.push d, rest) := by
  unfold MAX_SCRIPT_ELEMENT_SIZE at hd
  have hlen : ¬ (d.length + rest.length < d.length) := by omega
  unfold pushBytes OP_PUSHDATA1 OP_PUSHDATA2 OP_PUSHDATA4
  by_cases h1 : d.length < 76
  · rw [if_pos h1]
    simp only [List.cons_append, getOp, OP_PUSHDATA1, OP_PUSHDATA2, OP_PUSHDATA4, BitVec.toNat_ofNat, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp [h1, hlen]
    omega
  · rw [if_neg h1]
    by_cases h2 : d.length ≤ 0xff
    · rw [if_pos h2]
      simp only [List.cons_append, List.nil_append, getOp, OP_PUSHDATA1, OP_PUSHDATA2, OP_PUSHDATA4,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      rw [Nat.mod_eq_of_lt (by omega)]
      simp [hlen]
    · rw [if_neg h2, if_pos (by omega)]
      have hl : (BitcoinSer.leBytes 2 d.length ++ (d ++ rest)).length = 2 + (d.length + rest.length) := by
        simp [leBytes_len]
      simp only [List.cons_append, getOp, OP_PUSHDATA1, OP_PUSHDATA2, OP_PUSHDATA4, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, List.append_assoc]
      simp only [show (77:Nat) ≤ 78 from by omega, show ¬ ((77:Nat) < 76) from by omega, show (77:Nat) ≠ 76 from by omega,
        if_true, if_false, ite_true, ite_false, ne_eq, not_false_eq_true, not_true_eq_false]
      rw [if_neg (by rw [hl]; omega),
        List.take_left' (leBytes_len 2 _), List.drop_left' (leBytes_len 2 _), leVal_leBytes2 _ (by omega)]
      simp [hlen]

private theorem pushBytes_len_pos (d : Bytes) : 1 ≤ (pushBytes d).length := by
  unfold pushBytes
  by_cases h1 : d.length < OP_PUSHDATA1
  · rw [if_pos h1]; simp
  · rw [if_neg h1]
    by_cases h2 : d.length ≤ 0xff
    · rw [if_pos h2]; simp
    · rw [if_neg h2]; split <;> simp

private theorem pushesBytes_cons_ne_nil (p : Bytes) (ps : List Bytes) : pushesBytes (p :: ps) ≠ [] := by
  intro h
  have := congrArg List.length h
  simp only [pushesBytes, List.flatMap_cons, List.length_append, List.length_nil] at this
  have := pushBytes_len_pos p
  omega

private theorem parseScriptAux_nil (fuel : Nat) : parseScriptAux fuel [] = some [] := by
  cases fuel <;> rfl

private theorem parseScriptAux_cons (fuel : Nat) (s : Bytes) (hs : s ≠ []) :
    parseScriptAux (fuel + 1) s =
      match getOp s with
      | none => none
      | some (i, r) =>
        match parseScriptAux fuel r with
        | none => none
        | some is => some (i :: is) := by
  cases s with
  | nil => exact absurd rfl hs
  | cons b bs => rfl

private theorem isPushOnlyAux_cons (fuel : Nat) (s : Bytes) (hs : s ≠ []) :
    isPushOnlyAux (fuel + 1) s =
      match getOp s with
      | none => false
      | some (.push _, r) => isPushOnlyAux fuel r
      | some (.op c, r) => if BitcoinScript.OP_16 < c then false else isPushOnlyAux fuel r := by
  cases s with
  | nil => exact absurd rfl hs
  | cons b bs => rfl

private theorem parseScriptAux_pushes : ∀ (ps : List Bytes) (fuel : Nat), ps.length ≤ fuel →
    (∀ p ∈ ps, p.length ≤ MAX_SCRIPT_ELEMENT_SIZE) →
    parseScriptAux fuel (pushesBytes ps) = some (ps.map Instr.push)
  | [], fuel, _, _ => by cases fuel <;> rfl
  | p :: ps, fuel, hf, hp => by
    simp only [List.length_cons] at hf
    match fuel, hf with
    | f + 1, hf =>
      rw [parseScriptAux_cons _ _ (pushesBytes_cons_ne_nil p ps)]
      simp only [pushesBytes, List.flatMap_cons]
      rw [getOp_pushBytes p _ (hp p (List.mem_cons_self ..))]
      dsimp only
      have := parseScriptAux_pushes ps f (by omega) (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      simp only [pushesBytes] at this
      rw [this]
      rfl

private theorem pushesBytes_length_ge (ps : List Bytes) : ps.length ≤ (pushesBytes ps).length := by
  induction ps with
  | nil => simp [pushesBytes]
  | cons p ps ih =>
    simp only [pushesBytes, List.flatMap_cons, List.length_append, List.length_cons] at *
    have := pushBytes_len_pos p
    omega

private theorem isPushOnlyAux_pushes : ∀ (ps : List Bytes) (fuel : Nat), ps.length ≤ fuel →
    (∀ p ∈ ps, p.length ≤ MAX_SCRIPT_ELEMENT_SIZE) → isPushOnlyAux fuel (pushesBytes ps) = true
  | [], fuel, _, _ => by cases fuel <;> rfl
  | p :: ps, fuel, hf, hp => by
    simp only [List.length_cons] at hf
    match fuel, hf with
    | f + 1, hf =>
      rw [isPushOnlyAux_cons _ _ (pushesBytes_cons_ne_nil p ps)]
      simp only [pushesBytes, List.flatMap_cons]
      rw [getOp_pushBytes p _ (hp p (List.mem_cons_self ..))]
      have := isPushOnlyAux_pushes ps f (by omega) (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      simp only [pushesBytes] at this
      exact this

/-- A push-only scriptSig satisfies `IsPushOnly`. -/
theorem solution (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.isPushOnly (BitcoinVerify.pushesBytes ps) = true :=
  isPushOnlyAux_pushes ps _ (pushesBytes_length_ge ps) hp
