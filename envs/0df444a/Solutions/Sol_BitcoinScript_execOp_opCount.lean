-- Prove2me | solution 1 for BitcoinScript.execOp_opCount
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T05:49:30.735804+00:00
-- url     : https://prove2.me/submissions/3151bc47-7d6f-4ce9-9538-e62356c3ec15

import Definitions.Def_BitcoinScript

open BitcoinScript

/-- The tail of the binary numeric opcodes: `NUMEQUALVERIFY` pops or fails, every other one
pushes its result; `nOpCount` is untouched. -/
private theorem binary_tail (c : Byte) (s : State) (rest : List Bytes) (s' : State) (r : Int)
    (h : (if (c == OP_NUMEQUALVERIFY) = true then (if r ≠ 0 then some { s with stack := rest } else none)
          else some (pushNum { s with stack := rest } r)) = some s') :
    s.opCount ≤ s'.opCount ∧ (s'.opCount = s.opCount ∨ s'.opCount ≤ MAX_OPS_PER_SCRIPT) := by
  split at h
  · split at h
    · cases h; exact ⟨Nat.le_refl _, Or.inl rfl⟩
    · cases h
  · cases h; exact ⟨Nat.le_refl _, Or.inl rfl⟩

/-- No executed opcode lowers `nOpCount`, and any that raises it (`CHECKMULTISIG`) keeps it within
`MAX_OPS_PER_SCRIPT`. The proof is a case split along the opcode chain of `execOp`. -/
theorem solution (f : Flags) (o : Oracle) (e : Bool) (c : Byte) (s s' : State)
    (h : BitcoinScript.execOp f o e c s = some s') :
    s.opCount ≤ s'.opCount ∧ (s'.opCount = s.opCount ∨ s'.opCount ≤ BitcoinScript.MAX_OPS_PER_SCRIPT) := by
  unfold execOp at h
  by_cases h0 : (c == OP_1NEGATE || (OP_1 ≤ c && c ≤ OP_16)) = true
  · rw [if_pos h0] at h
    (try dsimp only at h)
    (repeat' split at h)
    all_goals (cases h)
    all_goals first
      | exact ⟨Nat.le_refl _, Or.inl rfl⟩
      | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
      | (constructor <;> simp_all <;> omega)
  · rw [if_neg h0] at h
    by_cases h1 : (c == OP_NOP) = true
    · rw [if_pos h1] at h
      (try dsimp only at h)
      (repeat' split at h)
      all_goals (cases h)
      all_goals first
        | exact ⟨Nat.le_refl _, Or.inl rfl⟩
        | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
        | (constructor <;> simp_all <;> omega)
    · rw [if_neg h1] at h
      by_cases h2 : (c == OP_CHECKLOCKTIMEVERIFY) = true
      · rw [if_pos h2] at h
        (try dsimp only at h)
        (repeat' split at h)
        all_goals (cases h)
        all_goals first
          | exact ⟨Nat.le_refl _, Or.inl rfl⟩
          | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
          | (constructor <;> simp_all <;> omega)
      · rw [if_neg h2] at h
        by_cases h3 : (c == OP_CHECKSEQUENCEVERIFY) = true
        · rw [if_pos h3] at h
          (try dsimp only at h)
          (repeat' split at h)
          all_goals (cases h)
          all_goals first
            | exact ⟨Nat.le_refl _, Or.inl rfl⟩
            | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
            | (constructor <;> simp_all <;> omega)
        · rw [if_neg h3] at h
          by_cases h4 : (c == OP_NOP1 || (OP_NOP4 ≤ c && c ≤ OP_NOP10)) = true
          · rw [if_pos h4] at h
            (try dsimp only at h)
            (repeat' split at h)
            all_goals (cases h)
            all_goals first
              | exact ⟨Nat.le_refl _, Or.inl rfl⟩
              | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
              | (constructor <;> simp_all <;> omega)
          · rw [if_neg h4] at h
            by_cases h5 : (c == OP_IF || c == OP_NOTIF) = true
            · rw [if_pos h5] at h
              (try dsimp only at h)
              (repeat' split at h)
              all_goals (cases h)
              all_goals first
                | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                | (constructor <;> simp_all <;> omega)
            · rw [if_neg h5] at h
              by_cases h6 : (c == OP_ELSE) = true
              · rw [if_pos h6] at h
                (try dsimp only at h)
                (repeat' split at h)
                all_goals (cases h)
                all_goals first
                  | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                  | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                  | (constructor <;> simp_all <;> omega)
              · rw [if_neg h6] at h
                by_cases h7 : (c == OP_ENDIF) = true
                · rw [if_pos h7] at h
                  (try dsimp only at h)
                  (repeat' split at h)
                  all_goals (cases h)
                  all_goals first
                    | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                    | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                    | (constructor <;> simp_all <;> omega)
                · rw [if_neg h7] at h
                  by_cases h8 : (c == OP_VERIFY) = true
                  · rw [if_pos h8] at h
                    (try dsimp only at h)
                    (repeat' split at h)
                    all_goals (cases h)
                    all_goals first
                      | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                      | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                      | (constructor <;> simp_all <;> omega)
                  · rw [if_neg h8] at h
                    by_cases h9 : (c == OP_RETURN) = true
                    · rw [if_pos h9] at h
                      (try dsimp only at h)
                      (repeat' split at h)
                      all_goals (cases h)
                      all_goals first
                        | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                        | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                        | (constructor <;> simp_all <;> omega)
                    · rw [if_neg h9] at h
                      by_cases h10 : (c == OP_TOALTSTACK) = true
                      · rw [if_pos h10] at h
                        (try dsimp only at h)
                        (repeat' split at h)
                        all_goals (cases h)
                        all_goals first
                          | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                          | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                          | (constructor <;> simp_all <;> omega)
                      · rw [if_neg h10] at h
                        by_cases h11 : (c == OP_FROMALTSTACK) = true
                        · rw [if_pos h11] at h
                          (try dsimp only at h)
                          (repeat' split at h)
                          all_goals (cases h)
                          all_goals first
                            | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                            | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                            | (constructor <;> simp_all <;> omega)
                        · rw [if_neg h11] at h
                          by_cases h12 : (c == OP_2DROP) = true
                          · rw [if_pos h12] at h
                            (try dsimp only at h)
                            (repeat' split at h)
                            all_goals (cases h)
                            all_goals first
                              | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                              | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                              | (constructor <;> simp_all <;> omega)
                          · rw [if_neg h12] at h
                            by_cases h13 : (c == OP_2DUP) = true
                            · rw [if_pos h13] at h
                              (try dsimp only at h)
                              (repeat' split at h)
                              all_goals (cases h)
                              all_goals first
                                | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                | (constructor <;> simp_all <;> omega)
                            · rw [if_neg h13] at h
                              by_cases h14 : (c == OP_3DUP) = true
                              · rw [if_pos h14] at h
                                (try dsimp only at h)
                                (repeat' split at h)
                                all_goals (cases h)
                                all_goals first
                                  | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                  | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                  | (constructor <;> simp_all <;> omega)
                              · rw [if_neg h14] at h
                                by_cases h15 : (c == OP_2OVER) = true
                                · rw [if_pos h15] at h
                                  (try dsimp only at h)
                                  (repeat' split at h)
                                  all_goals (cases h)
                                  all_goals first
                                    | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                    | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                    | (constructor <;> simp_all <;> omega)
                                · rw [if_neg h15] at h
                                  by_cases h16 : (c == OP_2ROT) = true
                                  · rw [if_pos h16] at h
                                    (try dsimp only at h)
                                    (repeat' split at h)
                                    all_goals (cases h)
                                    all_goals first
                                      | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                      | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                      | (constructor <;> simp_all <;> omega)
                                  · rw [if_neg h16] at h
                                    by_cases h17 : (c == OP_2SWAP) = true
                                    · rw [if_pos h17] at h
                                      (try dsimp only at h)
                                      (repeat' split at h)
                                      all_goals (cases h)
                                      all_goals first
                                        | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                        | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                        | (constructor <;> simp_all <;> omega)
                                    · rw [if_neg h17] at h
                                      by_cases h18 : (c == OP_IFDUP) = true
                                      · rw [if_pos h18] at h
                                        (try dsimp only at h)
                                        (repeat' split at h)
                                        all_goals (cases h)
                                        all_goals first
                                          | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                          | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                          | (constructor <;> simp_all <;> omega)
                                      · rw [if_neg h18] at h
                                        by_cases h19 : (c == OP_DEPTH) = true
                                        · rw [if_pos h19] at h
                                          (try dsimp only at h)
                                          (repeat' split at h)
                                          all_goals (cases h)
                                          all_goals first
                                            | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                            | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                            | (constructor <;> simp_all <;> omega)
                                        · rw [if_neg h19] at h
                                          by_cases h20 : (c == OP_DROP) = true
                                          · rw [if_pos h20] at h
                                            (try dsimp only at h)
                                            (repeat' split at h)
                                            all_goals (cases h)
                                            all_goals first
                                              | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                              | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                              | (constructor <;> simp_all <;> omega)
                                          · rw [if_neg h20] at h
                                            by_cases h21 : (c == OP_DUP) = true
                                            · rw [if_pos h21] at h
                                              (try dsimp only at h)
                                              (repeat' split at h)
                                              all_goals (cases h)
                                              all_goals first
                                                | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                | (constructor <;> simp_all <;> omega)
                                            · rw [if_neg h21] at h
                                              by_cases h22 : (c == OP_NIP) = true
                                              · rw [if_pos h22] at h
                                                (try dsimp only at h)
                                                (repeat' split at h)
                                                all_goals (cases h)
                                                all_goals first
                                                  | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                  | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                  | (constructor <;> simp_all <;> omega)
                                              · rw [if_neg h22] at h
                                                by_cases h23 : (c == OP_OVER) = true
                                                · rw [if_pos h23] at h
                                                  (try dsimp only at h)
                                                  (repeat' split at h)
                                                  all_goals (cases h)
                                                  all_goals first
                                                    | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                    | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                    | (constructor <;> simp_all <;> omega)
                                                · rw [if_neg h23] at h
                                                  by_cases h24 : (c == OP_PICK || c == OP_ROLL) = true
                                                  · rw [if_pos h24] at h
                                                    (try dsimp only at h)
                                                    (repeat' split at h)
                                                    all_goals (cases h)
                                                    all_goals first
                                                      | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                      | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                      | (constructor <;> simp_all <;> omega)
                                                  · rw [if_neg h24] at h
                                                    by_cases h25 : (c == OP_ROT) = true
                                                    · rw [if_pos h25] at h
                                                      (try dsimp only at h)
                                                      (repeat' split at h)
                                                      all_goals (cases h)
                                                      all_goals first
                                                        | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                        | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                        | (constructor <;> simp_all <;> omega)
                                                    · rw [if_neg h25] at h
                                                      by_cases h26 : (c == OP_SWAP) = true
                                                      · rw [if_pos h26] at h
                                                        (try dsimp only at h)
                                                        (repeat' split at h)
                                                        all_goals (cases h)
                                                        all_goals first
                                                          | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                          | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                          | (constructor <;> simp_all <;> omega)
                                                      · rw [if_neg h26] at h
                                                        by_cases h27 : (c == OP_TUCK) = true
                                                        · rw [if_pos h27] at h
                                                          (try dsimp only at h)
                                                          (repeat' split at h)
                                                          all_goals (cases h)
                                                          all_goals first
                                                            | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                            | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                            | (constructor <;> simp_all <;> omega)
                                                        · rw [if_neg h27] at h
                                                          by_cases h28 : (c == OP_SIZE) = true
                                                          · rw [if_pos h28] at h
                                                            (try dsimp only at h)
                                                            (repeat' split at h)
                                                            all_goals (cases h)
                                                            all_goals first
                                                              | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                              | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                              | (constructor <;> simp_all <;> omega)
                                                          · rw [if_neg h28] at h
                                                            by_cases h29 : (c == OP_EQUAL || c == OP_EQUALVERIFY) = true
                                                            · rw [if_pos h29] at h
                                                              (try dsimp only at h)
                                                              (repeat' split at h)
                                                              all_goals (cases h)
                                                              all_goals first
                                                                | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                                | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                                | (constructor <;> simp_all <;> omega)
                                                            · rw [if_neg h29] at h
                                                              by_cases h30 : (c == OP_1ADD || c == OP_1SUB || c == OP_NEGATE || c == OP_ABS || c == OP_NOT || c == OP_0NOTEQUAL) = true
                                                              · rw [if_pos h30] at h
                                                                cases hst : s.stack with
                                                                | nil => rw [hst] at h; cases h
                                                                | cons top rest =>
                                                                  rw [hst] at h
                                                                  dsimp only at h
                                                                  cases ht : toNum false nDefaultMaxNumSize top with
                                                                  | none => rw [ht] at h; cases h
                                                                  | some n => rw [ht] at h; cases h; exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                              · rw [if_neg h30] at h
                                                                by_cases h31 : (c == OP_ADD || c == OP_SUB || c == OP_BOOLAND || c == OP_BOOLOR || c == OP_NUMEQUAL || c == OP_NUMEQUALVERIFY || c == OP_NUMNOTEQUAL || c == OP_LESSTHAN || c == OP_GREATERTHAN || c == OP_LESSTHANOREQUAL || c == OP_GREATERTHANOREQUAL || c == OP_MIN || c == OP_MAX) = true
                                                                · rw [if_pos h31] at h
                                                                  cases hst : s.stack with
                                                                  | nil => rw [hst] at h; cases h
                                                                  | cons a rest1 =>
                                                                    cases rest1 with
                                                                    | nil => rw [hst] at h; cases h
                                                                    | cons b rest =>
                                                                      rw [hst] at h
                                                                      dsimp only at h
                                                                      cases hb : toNum false nDefaultMaxNumSize b with
                                                                      | none => rw [hb] at h; (try dsimp only at h); cases h
                                                                      | some n1 =>
                                                                        cases ha : toNum false nDefaultMaxNumSize a with
                                                                        | none => rw [hb, ha] at h; (try dsimp only at h); cases h
                                                                        | some n2 =>
                                                                          rw [hb, ha] at h
                                                                          dsimp only at h
                                                                          exact binary_tail c s rest s' _ h
                                                                · rw [if_neg h31] at h
                                                                  by_cases h32 : (c == OP_WITHIN) = true
                                                                  · rw [if_pos h32] at h
                                                                    (try dsimp only at h)
                                                                    (repeat' split at h)
                                                                    all_goals (cases h)
                                                                    all_goals first
                                                                      | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                                      | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                                      | (constructor <;> simp_all <;> omega)
                                                                  · rw [if_neg h32] at h
                                                                    by_cases h33 : (c == OP_RIPEMD160 || c == OP_SHA1 || c == OP_SHA256 || c == OP_HASH160 || c == OP_HASH256) = true
                                                                    · rw [if_pos h33] at h
                                                                      (try dsimp only at h)
                                                                      (repeat' split at h)
                                                                      all_goals (cases h)
                                                                      all_goals first
                                                                        | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                                        | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                                        | (constructor <;> simp_all <;> omega)
                                                                    · rw [if_neg h33] at h
                                                                      by_cases h34 : (c == OP_CODESEPARATOR) = true
                                                                      · rw [if_pos h34] at h
                                                                        (try dsimp only at h)
                                                                        (repeat' split at h)
                                                                        all_goals (cases h)
                                                                        all_goals first
                                                                          | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                                          | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                                          | (constructor <;> simp_all <;> omega)
                                                                      · rw [if_neg h34] at h
                                                                        by_cases h35 : (c == OP_CHECKSIG || c == OP_CHECKSIGVERIFY) = true
                                                                        · rw [if_pos h35] at h
                                                                          (try dsimp only at h)
                                                                          (repeat' split at h)
                                                                          all_goals (cases h)
                                                                          all_goals first
                                                                            | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                                            | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                                            | (constructor <;> simp_all <;> omega)
                                                                        · rw [if_neg h35] at h
                                                                          by_cases h36 : (c == OP_CHECKMULTISIG || c == OP_CHECKMULTISIGVERIFY) = true
                                                                          · rw [if_pos h36] at h
                                                                            (try dsimp only at h)
                                                                            (repeat' split at h)
                                                                            all_goals (cases h)
                                                                            all_goals first
                                                                              | exact ⟨Nat.le_refl _, Or.inl rfl⟩
                                                                              | (refine ⟨?_, Or.inr ?_⟩ <;> omega)
                                                                              | (constructor <;> simp_all <;> omega)
                                                                          · rw [if_neg h36] at h
                                                                            exact absurd h (by simp)
