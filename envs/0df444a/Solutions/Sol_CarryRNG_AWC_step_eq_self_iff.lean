-- Prove2me | solution 1 for CarryRNG.AWC.step_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:47:55.695258+00:00
-- url     : https://prove2.me/submissions/18d69734-efe7-4765-87d3-38f08aaf2100

import Mathlib
import Definitions.Def_CarryRNG_AWC_step
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

set_option autoImplicit false

namespace CarryRNG.AWC

lemma state_eq {b r : ℕ} (z w : State b r) (hx : ∀ i, (z.x i).val = (w.x i).val)
    (hc : z.c.val = w.c.val) : z = w := by
  cases z with
  | mk zx zc =>
  cases w with
  | mk wx wc =>
    have h1 : zx = wx := funext (fun i => Fin.ext (hx i))
    have h2 : zc = wc := Fin.ext hc
    subst h1; subst h2; rfl

/-- the sum `t = x_{r-s} + x_1 + c` -/
def tsum (b : ℕ) (L : Lags) (z : State b L.r) : ℕ :=
  (z.x ⟨L.r - L.s, by have := L.hs; have := L.hsr; omega⟩).val
    + (z.x ⟨0, by have := L.hs; have := L.hsr; omega⟩).val + z.c.val

lemma step_x_lt (b : ℕ) (L : Lags) (z : State b L.r) (i : Fin L.r) (hi : i.val + 1 < L.r) :
    (step b L z).x i = z.x ⟨i.val + 1, hi⟩ := by
  unfold step
  simp only [hi, dif_pos]

lemma step_x_last (b : ℕ) (L : Lags) (z : State b L.r) (i : Fin L.r) (hi : ¬ i.val + 1 < L.r) :
    ((step b L z).x i).val = if tsum b L z < b then tsum b L z else tsum b L z - b := by
  unfold step tsum
  simp only [hi, dif_neg, not_false_eq_true]
  split_ifs <;> rfl

lemma step_c (b : ℕ) (L : Lags) (z : State b L.r) :
    (step b L z).c.val = if tsum b L z < b then 0 else 1 := by
  unfold step tsum
  simp only
  split_ifs <;> rfl


theorem step_eq_self_iff' (b : ℕ) (L : Lags) (hb : 2 ≤ b) (z : State b L.r) :
    step b L z = z ↔ z = zeroSeed b L.r hb ∨ z = topSeed b L.r hb := by
  have hs := L.hs
  have hsr := L.hsr
  constructor
  · intro h
    have hx : ∀ i : Fin L.r, ∀ hi : i.val + 1 < L.r, z.x ⟨i.val + 1, hi⟩ = z.x i := by
      intro i hi
      have := congrArg (fun w : State b L.r => w.x i) h
      simp only [step_x_lt b L z i hi] at this
      exact this
    have hconst : ∀ i : Fin L.r, (z.x i).val = (z.x ⟨0, by omega⟩).val := by
      intro i
      obtain ⟨i, hi⟩ := i
      induction i with
      | zero => rfl
      | succ n ih =>
        have := hx ⟨n, by omega⟩ (by simp; omega)
        rw [show (⟨n + 1, hi⟩ : Fin L.r) = ⟨(⟨n, by omega⟩ : Fin L.r).val + 1, by simp; omega⟩ from rfl,
          this]
        exact ih (by omega)
    set v := (z.x ⟨0, by omega⟩).val with hv
    have hlast := congrArg (fun w : State b L.r => (w.x ⟨L.r - 1, by omega⟩).val) h
    simp only [step_x_last b L z ⟨L.r - 1, by omega⟩ (by simp; omega)] at hlast
    have hcc := congrArg (fun w : State b L.r => w.c.val) h
    simp only [step_c] at hcc
    have ht : tsum b L z = v + v + z.c.val := by
      unfold tsum
      rw [hconst ⟨L.r - L.s, by omega⟩]
    have hlv : (z.x ⟨L.r - 1, by omega⟩).val = v := hconst _
    have hc2 : z.c.val < 2 := z.c.isLt
    have hvb : v < b := (z.x ⟨0, by omega⟩).isLt
    rw [hlv, ht] at hlast
    rw [ht] at hcc
    by_cases hlt : v + v + z.c.val < b
    · left
      simp only [hlt, if_true] at hlast hcc
      apply state_eq
      · intro i; rw [hconst i]; simp [zeroSeed]; omega
      · simp [zeroSeed]; omega
    · right
      simp only [hlt, if_false] at hlast hcc
      apply state_eq
      · intro i; rw [hconst i]; simp [topSeed]; omega
      · simp [topSeed]; omega
  · rintro (h | h)
    · subst h
      apply state_eq
      · intro i
        by_cases hi : i.val + 1 < L.r
        · rw [step_x_lt b L _ i hi]; simp [zeroSeed]
        · rw [step_x_last b L _ i hi]; simp [tsum, zeroSeed]
      · rw [step_c]; simp [tsum, zeroSeed]; omega
    · subst h
      apply state_eq
      · intro i
        by_cases hi : i.val + 1 < L.r
        · rw [step_x_lt b L _ i hi]; simp [topSeed]
        · rw [step_x_last b L _ i hi]; simp [tsum, topSeed]
          split_ifs <;> omega
      · rw [step_c]; simp [tsum, topSeed]; omega

end CarryRNG.AWC

theorem solution (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    CarryRNG.AWC.step b L z = z ↔ z = CarryRNG.AWC.zeroSeed b L.r hb ∨ z = CarryRNG.AWC.topSeed b L.r hb :=
  CarryRNG.AWC.step_eq_self_iff' b L hb z
