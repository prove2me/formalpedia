-- Prove2me | solution 1 for BitDFT.guard_log_from_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:53:31.825034+00:00
-- url     : https://prove2.me/submissions/f23c9943-e4f1-4f62-9125-8219f18ac739

import Definitions.Def_IntMul_MultitapeModel

/-- The ceiling logarithm is determined by the binary field length and its power-of-two flag. -/
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    IntMul.lg n = max (if n = 2^(n.size-1) then n.size-1 else n.size) 1 := by
  unfold IntMul.lg
  by_cases h : n = 2^(n.size-1)
  · rw [if_pos h]
    congr 1
    calc
      Nat.clog 2 n = Nat.clog 2 (2^(n.size-1)) := congrArg (Nat.clog 2) h
      _ = n.size-1 := Nat.clog_pow 2 (n.size-1) (by decide)
  · rw [if_neg h]
    have hs : 0 < n.size := Nat.size_pos.mpr (by omega)
    have hlo : 2^(n.size-1) ≤ n := Nat.lt_size.mp (by omega)
    have hlt : 2^(n.size-1) < n := by omega
    have hclo : n.size-1 < Nat.clog 2 n :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr hlt
    have hchi : Nat.clog 2 n ≤ n.size :=
      Nat.clog_le_of_le_pow (Nat.lt_size_self n).le
    have hc : Nat.clog 2 n = n.size := by omega
    rw [hc]
