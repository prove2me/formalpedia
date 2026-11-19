-- Prove2me | solution 1 for DeletionCode.DescriptionCount.description_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:58:45.797183+00:00
-- url     : https://prove2.me/submissions/21cbbd1a-3003-4fd1-9800-03fd73f9aa00

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_DescriptionCount
import Theorems.Thm_DeletionCode_DescriptionCount_description_card

set_option autoImplicit true
open DeletionCode DeletionCode.DescriptionCount
namespace DeletionCode.DescriptionCount
theorem _root_.solution (n L ν c : ℕ)
    (hL : 1 ≤ L) (hν : 1 ≤ ν) (hc : c ≤ ν) :
    Fintype.card (Description n L ν c) ≤
      n ^ c * (fieldBound L ν) ^ (50 * ν) := by
  let B := fieldBound L ν
  have hmul : ν ≤ L * ν := by
    calc
      ν = 1 * ν := (one_mul ν).symm
      _ ≤ L * ν := Nat.mul_le_mul_right ν hL
  have hB : 1 ≤ B := by
    dsimp [B, fieldBound]
    nlinarith
  have hheader : 4 * L ≤ B := by
    dsimp [B, fieldBound]
    nlinarith
  have hname : ν ≤ B := by
    dsimp [B, fieldBound]
    nlinarith
  have hp1 : (4 * L) ^ ν ≤ B ^ ν := by gcongr
  have hp2 : ν ^ c ≤ B ^ ν := by
    calc
      ν ^ c ≤ B ^ c := by gcongr
      _ ≤ B ^ ν := by gcongr
  have hpower : B ^ ν * B ^ ν * (B ^ 12) ^ (4 * ν) = B ^ (50 * ν) := by
    rw [← pow_add, ← pow_mul, ← pow_add]
    congr 1
    omega
  calc
    Fintype.card (Description n L ν c) =
        n ^ c * ((4 * L) ^ ν * ν ^ c * (B ^ 12) ^ (4 * ν)) := by
          rw [description_card]
          dsimp [B]
          ring
    _ ≤ n ^ c * (B ^ ν * B ^ ν * (B ^ 12) ^ (4 * ν)) := by gcongr
    _ = n ^ c * B ^ (50 * ν) := by rw [hpower]
end DeletionCode.DescriptionCount
