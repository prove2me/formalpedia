-- Prove2me | solution 1 for DeletionCode.CountExponent.field_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:17.716+00:00
-- url     : https://prove2.me/submissions/78f4181d-c364-4c40-927a-7b121b771122

import Definitions.Def_DeletionCode_DescriptionCount
import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_CountExponent
section
namespace DeletionCode.CountExponent
open DescriptionCount HeaderRecovery
private theorem self_le_power (base : ℕ) (hbase : 2 ≤ base) : ∀ q, q ≤ base ^ q := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hp : 1 ≤ base ^ q := one_le_pow₀ (by omega)
    calc
      q + 1 ≤ base ^ q + base ^ q := by omega
      _ = 2 * base ^ q := by omega
      _ ≤ base * base ^ q := Nat.mul_le_mul_right _ hbase
      _ = base ^ (q + 1) := by rw [pow_succ, Nat.mul_comm]
end DeletionCode.CountExponent
end

set_option autoImplicit true
open DeletionCode DeletionCode.CountExponent
open DescriptionCount HeaderRecovery
namespace DeletionCode.CountExponent
theorem _root_.solution (k t R : ℕ) (hR : 1 ≤ R) :
    fieldBound (windowLength k) (2 * t * R) ^ (50 * (2 * t * R)) ≤
      (windowLength k * R) ^ (exponent t * R) := by
  let L := windowLength k
  let C := 16 * (2 * t + 1)
  have hL : 3 ≤ L := by dsimp [L, windowLength]; omega
  have hbase : 2 ≤ L * R := by nlinarith
  have hC : C ≤ (L * R) ^ C := self_le_power (L * R) hbase C
  have hfield : fieldBound L (2 * t * R) ≤ C * (L * R) := by
    have hinner : 2 * t * R + 1 ≤ (2 * t + 1) * R := by nlinarith
    calc
      fieldBound L (2 * t * R) = 16 * L * (2 * t * R + 1) := rfl
      _ ≤ 16 * L * ((2 * t + 1) * R) := Nat.mul_le_mul_left _ hinner
      _ = C * (L * R) := by dsimp [C]; ring
  have hb : fieldBound L (2 * t * R) ≤ (L * R) ^ (C + 1) := by
    calc
      fieldBound L (2 * t * R) ≤ C * (L * R) := hfield
      _ ≤ (L * R) ^ C * (L * R) := Nat.mul_le_mul_right _ hC
      _ = (L * R) ^ (C + 1) := (pow_succ _ _).symm
  change fieldBound L (2 * t * R) ^ (50 * (2 * t * R)) ≤ (L * R) ^ (exponent t * R)
  calc
    _ ≤ ((L * R) ^ (C + 1)) ^ (50 * (2 * t * R)) := by gcongr
    _ = (L * R) ^ (exponent t * R) := by
      rw [← pow_mul]
      congr 1
      dsimp [C, exponent]
      ring
end DeletionCode.CountExponent
