-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.repeatFactorRay_periodicFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:29.377562+00:00
-- url     : https://prove2.me/submissions/c87571f3-5ee6-4a84-b929-f93c6680b1e1

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Theorems.Thm_DeciSigma1_Holes_Tail_shift_mul
public import Theorems.Thm_DeciSigma1_Holes_Tail_repeatFactorRay_period
public import Theorems.Thm_DeciSigma1_Holes_Tail_repeatFactorRay_agrees
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_mod
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_RayAgrees_getElem__ac7111bad97d


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hcl : ClosedAt T q0 x B c c') {p : ℕ}
    (hp : 0 < p)
    (hdvd : p ∣ c' - c) (hper : PeriodicOn x p (c - B) c') :
    PeriodicFrom (repeatFactorRay x c c' hcl.2.1 hcl.2.2.1).stream (c - B) p := by
  classical
  have hcc := hcl.2.1; have hc' := hcl.2.2.1; have hB := hcl.1
  set Ω := repeatFactorRay x c c' hcc hc'
  set h := c' - c
  have hh : 0 < h := by omega
  have hag := repeatFactorRay_agrees hcc hc'
  have hmul := shift_mul (f := Ω.stream) (A := c - B) (h := h) (repeatFactorRay_period hcl)
  -- every position from `c - B` on reduces into `[c - B, c' - B)`
  have hred : ∀ y, c - B ≤ y → Ω.stream y = Ω.stream (c - B + (y - (c - B)) % h) := by
    intro y hy
    have := hmul ((y - (c - B)) / h) (c - B + (y - (c - B)) % h) (by omega)
    rw [← this]; congr 1
    have := Nat.mod_add_div (y - (c - B)) h
    rw [Nat.mul_comm] at this; omega
  intro t
  change Ω.stream (c - B + (t + p)) = Ω.stream (c - B + t)
  rw [hred _ (by omega), hred (c - B + t) (by omega)]
  have h1 : (c - B + (c - B + (t + p) - (c - B)) % h) < c' := by
    have := Nat.mod_lt (c - B + (t + p) - (c - B)) hh; omega
  have h2 : (c - B + (c - B + t - (c - B)) % h) < c' := by
    have := Nat.mod_lt (c - B + t - (c - B)) hh; omega
  have e := hper.eq_of_mod (p := c - B + (c - B + (t + p) - (c - B)) % h)
    (q := c - B + (c - B + t - (c - B)) % h) (by omega) (by omega) h1 h2 (by
      rw [show c - B + (t + p) - (c - B) = t + p by omega, show c - B + t - (c - B) = t by omega]
      obtain ⟨j, hj⟩ := hdvd
      rw [Nat.add_mod (c - B), Nat.add_mod (c - B) (t % h), hj, Nat.mod_mul_right_mod,
        Nat.mod_mul_right_mod, Nat.add_mod t p, Nat.mod_self, Nat.add_zero, Nat.mod_mod])
  rw [hag.getElem? h1, hag.getElem? h2] at e
  exact (Option.some.inj e)
end DeciSigma1.Holes.Tail
