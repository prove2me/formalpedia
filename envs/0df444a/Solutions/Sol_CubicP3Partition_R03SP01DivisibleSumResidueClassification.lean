-- Prove2me | solution 1 for CubicP3Partition.R03SP01DivisibleSumResidueClassification
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:30:38.471634+00:00
-- url     : https://prove2.me/submissions/fbcd7eba-90bf-40a0-9329-a8549078629f

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

set_option maxHeartbeats 1000000


end CubicP3Partition

open CubicP3Partition
theorem solution
    (a b : Nat) (h : 3 ∣ a + b) :
    (∃ kA kB : Nat, a = kA * 3 ∧ b = kB * 3) ∨
    (∃ kA kB : Nat, a = 1 + kA * 3 ∧ b = 2 + kB * 3) ∨
    (∃ kA kB : Nat, a = 2 + kA * 3 ∧ b = 1 + kB * 3) := by
  obtain ⟨q, hq⟩ := h
  have ha := Nat.mod_add_div a 3
  have hb := Nat.mod_add_div b 3
  have hla := Nat.mod_lt a (by omega : 0 < 3)
  have hlb := Nat.mod_lt b (by omega : 0 < 3)
  have hm : (a + b) % 3 = 0 := by
    rw [hq]
    simp
  have ham := Nat.add_mod a b 3
  by_cases ha0 : a % 3 = 0
  · by_cases hb0 : b % 3 = 0
    · left
      exact ⟨a / 3, b / 3, by omega, by omega⟩
    · by_cases hb1 : b % 3 = 1
      · exfalso
        omega
      · have hb2 : b % 3 = 2 := by omega
        exfalso
        omega
  · by_cases ha1 : a % 3 = 1
    · by_cases hb0 : b % 3 = 0
      · exfalso
        omega
      · by_cases hb1 : b % 3 = 1
        · exfalso
          omega
        · have hb2 : b % 3 = 2 := by omega
          right
          left
          exact ⟨a / 3, b / 3, by omega, by omega⟩
    · have ha2 : a % 3 = 2 := by omega
      by_cases hb0 : b % 3 = 0
      · exfalso
        omega
      · by_cases hb1 : b % 3 = 1
        · right
          right
          exact ⟨a / 3, b / 3, by omega, by omega⟩
        · have hb2 : b % 3 = 2 := by omega
          exfalso
          omega

