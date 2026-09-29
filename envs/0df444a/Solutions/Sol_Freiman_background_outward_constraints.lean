-- Prove2me | solution 1 for Freiman.background_outward_constraints
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:05:15.542698+00:00
-- url     : https://prove2.me/submissions/1aaf4b7a-0309-4874-b136-c745687b7435

import Definitions.Def_Freiman_backgroundWords
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

open Freiman
namespace BackgroundOutwardSep10
private theorem prepend_right (a : ℤ → ℕ+) (i : ℤ) (hi : (a i : ℕ) = 3) (n : ℕ) :
    (backgroundPrepend [3] (backgroundOutward a i true) n : ℕ) = (a (i+(n:ℤ)) : ℕ) := by
  cases n with
  | zero => simpa [backgroundPrepend] using hi.symm
  | succ n => simp [backgroundPrepend, backgroundOutward, Nat.cast_add, add_assoc]
private theorem prepend_left (a : ℤ → ℕ+) (i : ℤ) (hi : (a i : ℕ) = 3) (n : ℕ) :
    (backgroundPrepend [3] (backgroundOutward a i false) n : ℕ) = (a (i-(n:ℤ)) : ℕ) := by
  cases n with
  | zero => simpa [backgroundPrepend] using hi.symm
  | succ n => simp [backgroundPrepend, backgroundOutward, Nat.cast_add, sub_add_eq_sub_sub]
end BackgroundOutwardSep10
open BackgroundOutwardSep10

theorem solution (a : ℤ → ℕ+) (i : ℤ)
    (ha : ∀ j : ℤ, (a j : ℕ) ≤ 4)
    (h14 : AvoidsBlock a [1,4]) (h41 : AvoidsBlock a [4,1])
    (h31313 : AvoidsBlock a [3,1,3,1,3]) (hi : (a i : ℕ) = 3) :
    ∀ r : Bool,
      (∀ n : ℕ, (backgroundOutward a i r n : ℕ) ≤ 4) ∧
      OneSidedAvoidsBlock (backgroundOutward a i r) [1,4] ∧
      OneSidedAvoidsBlock (backgroundPrepend [3] (backgroundOutward a i r)) [3,1,3,1,3] := by
  intro r
  refine ⟨?_, ?_, ?_⟩
  · intro n
    cases r <;> exact ha _
  · intro n hm
    have hm0 := hm 0 (by decide)
    have hm1 := hm 1 (by decide)
    cases r
    · change (a (i-(n:ℤ)-1) : ℕ) = 1 at hm0
      change (a (i-((n+1:ℕ):ℤ)-1) : ℕ) = 4 at hm1
      have hn1 : i-((n+1:ℕ):ℤ)-1 = i-(n:ℤ)-2 := by omega
      rw [hn1] at hm1
      apply h41 (i-(n:ℤ)-2)
      intro k hk
      have hk' : k < 2 := hk
      interval_cases k
      · change (a (i-(n:ℤ)-2+0) : ℕ) = 4
        simpa using hm1
      · change (a (i-(n:ℤ)-2+1) : ℕ) = 1
        have hidx : i-(n:ℤ)-2+1 = i-(n:ℤ)-1 := by omega
        simpa only [hidx] using hm0
    · change (a (i+(n:ℤ)+1) : ℕ) = 1 at hm0
      change (a (i+((n+1:ℕ):ℤ)+1) : ℕ) = 4 at hm1
      apply h14 (i+(n:ℤ)+1)
      intro k hk
      have hk' : k < 2 := hk
      interval_cases k
      · change (a (i+(n:ℤ)+1+0) : ℕ) = 1
        simpa using hm0
      · change (a (i+(n:ℤ)+1+1) : ℕ) = 4
        simpa [Nat.cast_add, add_assoc] using hm1
  · intro n hm
    cases r
    · apply h31313 (i-(n:ℤ)-4)
      intro k hk
      have hk' : k < 5 := hk
      interval_cases k
      · have h := hm 4 (by decide)
        rw [prepend_left a i hi] at h
        change (a (i-((n+4:ℕ):ℤ)) : ℕ) = 3 at h
        change (a (i-(n:ℤ)-4+0) : ℕ) = 3
        have hidx : i-(n:ℤ)-4+0 = i-((n+4:ℕ):ℤ) := by omega
        simpa only [hidx] using h
      · have h := hm 3 (by decide)
        rw [prepend_left a i hi] at h
        change (a (i-((n+3:ℕ):ℤ)) : ℕ) = 1 at h
        change (a (i-(n:ℤ)-4+1) : ℕ) = 1
        have hidx : i-(n:ℤ)-4+1 = i-((n+3:ℕ):ℤ) := by omega
        simpa only [hidx] using h
      · have h := hm 2 (by decide)
        rw [prepend_left a i hi] at h
        change (a (i-((n+2:ℕ):ℤ)) : ℕ) = 3 at h
        change (a (i-(n:ℤ)-4+2) : ℕ) = 3
        have hidx : i-(n:ℤ)-4+2 = i-((n+2:ℕ):ℤ) := by omega
        simpa only [hidx] using h
      · have h := hm 1 (by decide)
        rw [prepend_left a i hi] at h
        change (a (i-((n+1:ℕ):ℤ)) : ℕ) = 1 at h
        change (a (i-(n:ℤ)-4+3) : ℕ) = 1
        have hidx : i-(n:ℤ)-4+3 = i-((n+1:ℕ):ℤ) := by omega
        simpa only [hidx] using h
      · have h := hm 0 (by decide)
        rw [prepend_left a i hi] at h
        change (a (i-((n+0:ℕ):ℤ)) : ℕ) = 3 at h
        change (a (i-(n:ℤ)-4+4) : ℕ) = 3
        have hidx : i-(n:ℤ)-4+4 = i-((n+0:ℕ):ℤ) := by omega
        simpa only [hidx] using h
    · apply h31313 (i+(n:ℤ))
      intro k hk
      have h := hm k hk
      simp only [prepend_right a i hi] at h
      simpa only [Nat.cast_add, add_assoc] using h

#print axioms solution
