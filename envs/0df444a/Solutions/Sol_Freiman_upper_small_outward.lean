-- Prove2me | solution 1 for Freiman.upper_small_outward
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:19:36.08845+00:00
-- url     : https://prove2.me/submissions/f895324e-6a35-46cc-98c6-af391156d5ff

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_KA_bounds

open Freiman

private theorem pad_right (n : ℕ+) (l r : ℕ → ℕ+) (j k : ℕ) :
    upperPad (upperCentral n l r) j ((k : ℤ)+1) = if k+1 ≤ j then r k else 3 := by
  have habs : ((k : ℤ)+1).natAbs=k+1 := by omega
  have hnat : ((k : ℤ)+1).toNat-1=k := by omega
  simp only [upperPad,habs]
  split_ifs
  · rw [upperCentral,if_neg (by omega),if_pos (by omega),hnat]
  · rfl

private theorem pad_reflection (n : ℕ+) (l r : ℕ → ℕ+) (j : ℕ) (i : ℤ) :
    upperPad (upperCentral n l r) j (-i) = upperPad (upperCentral n r l) j i := by
  by_cases hz : i = 0
  · simp [hz, upperPad, upperCentral]
  by_cases hp : 0 < i
  · simp [upperPad, upperCentral, hz, hp, neg_ne_zero.mpr hz, show ¬i < 0 by omega]
  · have hn : i < 0 := by omega
    simp [upperPad, upperCentral, hz, hp, neg_ne_zero.mpr hz, hn]

private theorem one_admissible (r : ℕ → ℕ+) (hr : upperAdmissible r)
    (hr0 : (r 0 : ℕ) ≤ 3) : upperAdmissible (upperOne r) := by
  constructor
  · intro k
    cases k with
    | zero => norm_num [upperOne]
    | succ k => exact hr.1 k
  · intro k hk
    cases k with
    | zero => exact hr0
    | succ k => exact hr.2 k hk

private theorem pad_admissible (r : ℕ → ℕ+) (hr : upperAdmissible r) (j : ℕ) :
    upperAdmissible (fun k : ℕ => if k+1 ≤ j then r k else 3) := by
  constructor
  · intro k
    dsimp only
    split_ifs
    · exact hr.1 k
    · norm_num
  · intro k hk
    dsimp only at hk ⊢
    have hin : k+1 ≤ j := by
      by_contra hh
      rw [if_neg hh] at hk
      norm_num at hk
    rw [if_pos hin] at hk
    split_ifs
    · exact hr.2 k hk
    · norm_num

private theorem shift_admissible (r : ℕ → ℕ+) (hr : upperAdmissible r) (k : ℕ) :
    upperAdmissible (fun m => r (m+k)) := by
  constructor
  · intro m
    exact hr.1 (m+k)
  · intro m hm
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr.2 (m+k) hm

private theorem positive_outward (l r : ℕ → ℕ+) (hr : upperAdmissible r)
    (hr0 : (r 0 : ℕ) ≤ 3) (j k : ℕ) :
    cfValue (fun m : ℕ => upperPad (upperCentral 4 (upperOne l) (upperOne r)) j
      ((k:ℤ)+1+(m:ℤ)+1)) ≤ upperTheta1 := by
  let b : ℕ → ℕ+ := fun m => if m+1 ≤ j then upperOne r m else 3
  have hb : upperAdmissible b := pad_admissible _ (one_admissible r hr hr0) j
  have heq : (fun m : ℕ => upperPad (upperCentral 4 (upperOne l) (upperOne r)) j
      ((k:ℤ)+1+(m:ℤ)+1)) = (fun m => b (m+(k+1))) := by
    funext m
    have heq : (k:ℤ)+1+(m:ℤ)+1 = ((m+(k+1):ℕ):ℤ)+1 := by omega
    rw [heq, pad_right]
  rw [heq]
  exact (upper_KA_bounds _ ⟨_, shift_admissible b hb (k+1), rfl⟩).2

theorem solution (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hl0 : (l 0 : ℕ) ≤ 3)
    (hr : upperAdmissible r) (hr0 : (r 0 : ℕ) ≤ 3) (j : ℕ) (i : ℤ) (hi : i ≠ 0)
    (h4 : (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j i : ℕ) = 4) :
    upperOutward (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j) i ≤ upperTheta1 := by
  clear h4
  by_cases hip : 0 < i
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, i = (k:ℤ)+1 := ⟨i.toNat-1, by omega⟩
    rw [upperOutward, if_pos hip, hk]
    exact positive_outward l r hr hr0 j k
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, -i = (k:ℤ)+1 := ⟨(-i).toNat-1, by omega⟩
    have hb := positive_outward r l hl hl0 j k
    rw [← hk] at hb
    have heq : (fun m : ℕ => upperPad (upperCentral 4 (upperOne r) (upperOne l)) j (-i+(m:ℤ)+1)) =
        (fun m : ℕ => upperPad (upperCentral 4 (upperOne l) (upperOne r)) j (i-(m:ℤ)-1)) := by
      funext m
      rw [← pad_reflection]
      congr 1
      omega
    simpa only [upperOutward, if_neg hip, heq] using hb
