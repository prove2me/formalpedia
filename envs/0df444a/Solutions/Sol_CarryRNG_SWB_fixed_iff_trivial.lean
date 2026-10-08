-- Prove2me | solution 1 for CarryRNG.SWB.fixed_iff_trivial
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:47:24.44654+00:00
-- url     : https://prove2.me/submissions/efb8ef2f-d160-495c-b319-674ac6022d73

import Mathlib
import Definitions.Def_CarryRNG_SWB_step
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

open CarryRNG.AWC CarryRNG.SWB

theorem solution (b : ℕ) (L : Lags) (hb : 2 ≤ b) (z : State b L.r) :
    step b L hb z = z ↔ z = zeroSeed b L.r hb ∨ z = topSeed b L.r hb := by
  have hs := L.hs
  have hsr := L.hsr
  have hr : 0 < L.r := by omega
  constructor
  · intro hz
    have shift (i : Fin L.r) (hi : i.val + 1 < L.r) :
        z.x ⟨i.val + 1, hi⟩ = z.x i := by
      have h := congrArg (fun w : State b L.r => w.x i) hz
      simpa [step, hi] using h
    have constant (i : Fin L.r) : z.x i = z.x ⟨0, hr⟩ := by
      obtain ⟨i, hi⟩ := i
      induction i with
      | zero => rfl
      | succ i ih =>
        exact (shift ⟨i, by omega⟩ hi).trans (ih (by omega))
    have ha := constant ⟨L.r - L.s, by omega⟩
    have hd := (z.x ⟨0, hr⟩).isLt
    have hc := z.c.isLt
    have hx := congrArg (fun w : State b L.r => (w.x ⟨L.r - 1, by omega⟩).val) hz
    have hcarry := congrArg (fun w : State b L.r => w.c.val) hz
    have he := constant ⟨L.r - 1, by omega⟩
    have hlast : ¬ (L.r - 1 + 1 < L.r) := by omega
    by_cases hzero : z.c.val = 0
    · left
      have hv : (z.x ⟨0, hr⟩).val = 0 := by
        simp [step, ha, hzero, he, hlast] at hx
        omega
      cases z with
      | mk x c =>
        congr 1
        · funext i
          apply Fin.ext
          have h := congrArg Fin.val (constant i)
          simpa [zeroSeed] using h.trans hv
        · apply Fin.ext; exact hzero
    · right
      have hone : z.c.val = 1 := by omega
      have hv : (z.x ⟨0, hr⟩).val = b - 1 := by
        simp [step, ha, hone, he, hlast] at hx
        omega
      cases z with
      | mk x c =>
        congr 1
        · funext i
          apply Fin.ext
          have h := congrArg Fin.val (constant i)
          simpa [topSeed] using h.trans hv
        · apply Fin.ext; exact hone
  · rintro (rfl | rfl)
    · simp only [step, zeroSeed]
      congr 1
      funext i
      split <;> rfl
    · simp only [step, topSeed]
      have hd : b - 1 < b - 1 + 1 := by omega
      simp only [Fin.val_one, hd, decide_true, ↓reduceIte]
      congr 1
      funext i
      split
      · rfl
      · apply Fin.ext
        dsimp
        omega

#print axioms solution
