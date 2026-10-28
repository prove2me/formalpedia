-- Prove2me | solution 1 for BitcoinVerify.isWitnessProgram_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:42:30.787099+00:00
-- url     : https://prove2.me/submissions/bf10851f-2e39-4e37-87c4-102e44bcb4b8

import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
theorem S189B_tn (k : Nat) (h : k < 256) : (BitVec.ofNat 8 k).toNat = k := by
  simp [BitVec.toNat_ofNat]; omega

theorem S189B_pb_small (d : Bytes) (h : d.length < 76) : pushBytes d = BitVec.ofNat 8 d.length :: d := by
  simp [pushBytes, OP_PUSHDATA1, h]

theorem S189B_wb_eq (v : Nat) (prog : Bytes) (hp : prog.length < 76) :
    witnessBytes v prog = BitVec.ofNat 8 (if v = 0 then 0 else 0x50 + v) :: BitVec.ofNat 8 prog.length :: prog := by
  simp [witnessBytes, S189B_pb_small prog hp]

theorem S189B_iwp_wb (v : Nat) (prog : Bytes) (hv : v ≤ 16) (h2 : 2 ≤ prog.length) (h40 : prog.length ≤ 40) :
    isWitnessProgram (witnessBytes v prog) = some (v, prog) := by
  rw [S189B_wb_eq _ _ (by omega)]
  have e0 : (BitVec.ofNat 8 (if v = 0 then 0 else 0x50 + v)).toNat = if v = 0 then 0 else 0x50 + v :=
    S189B_tn _ (by split <;> omega)
  have e1 : (BitVec.ofNat 8 prog.length).toNat = prog.length := S189B_tn _ (by omega)
  unfold isWitnessProgram
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons, List.drop_succ_cons,
    List.drop_zero]
  rw [e0, e1]
  rw [if_neg (by omega), if_neg (by split <;> omega), if_pos (by omega)]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  unfold decodeOpN
  split <;> simp_all <;> omega

theorem S189B_iwp_iff (s : Bytes) (v : Nat) (prog : Bytes) :
    BitcoinVerify.isWitnessProgram s = some (v, prog) ↔
      v ≤ 16 ∧ 2 ≤ prog.length ∧ prog.length ≤ 40 ∧ s = BitcoinVerify.witnessBytes v prog := by
  constructor
  · intro H
    rcases s with _ | ⟨a0, _ | ⟨a1, t⟩⟩
    · simp [isWitnessProgram] at H
    · simp [isWitnessProgram] at H
    unfold isWitnessProgram at H
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons, List.drop_succ_cons,
      List.drop_zero] at H
    split at H
    · simp at H
    split at H
    · simp at H
    split at H
    · rename_i hA hB hC
      simp only [Option.some.injEq, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      have ha0 := a0.isLt
      have ha1 := a1.isLt
      have hv : decodeOpN a0.toNat ≤ 16 := by unfold decodeOpN; split <;> omega
      refine ⟨hv, by omega, by omega, ?_⟩
      rw [S189B_wb_eq _ _ (by omega)]
      congr 1
      · apply BitVec.eq_of_toNat_eq
        unfold decodeOpN
        rcases Nat.eq_zero_or_pos a0.toNat with hz | hz
        · simp [hz]
        · rw [if_neg (show ¬ a0.toNat = 0 by omega)]; rw [if_neg (by omega), S189B_tn _ (by omega)]; omega
      · congr 1
        apply BitVec.eq_of_toNat_eq
        rw [S189B_tn _ (by omega)]; omega
    · simp at H
  · rintro ⟨hv, h2, h40, rfl⟩
    exact S189B_iwp_wb v prog hv h2 h40

open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
theorem solution (s : Bytes) (v : Nat) (prog : Bytes) :
    BitcoinVerify.isWitnessProgram s = some (v, prog) ↔
      v ≤ 16 ∧ 2 ≤ prog.length ∧ prog.length ≤ 40 ∧ s = BitcoinVerify.witnessBytes v prog := by
  exact S189B_iwp_iff s v prog
