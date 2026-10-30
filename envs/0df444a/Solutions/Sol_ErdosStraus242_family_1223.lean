-- Prove2me | solution 1 for ErdosStraus242.family_1223
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T23:00:59.462993+00:00
-- url     : https://prove2.me/submissions/a3b87819-187e-4d8e-b6b4-afde54b9cf37

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

open ErdosStraus242

theorem solution (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hmod : p % 1223 = 1222) : IsErdosStraus p := by
  let k := p / 1223 + 1
  have hpk : p + 1 = 1223 * k := by
    have := Nat.mod_add_div p 1223
    dsimp [k]
    omega
  have hk : 1 < k := by
    by_contra h
    have heq : p = 1222 := by dsimp [k] at *; omega
    subst p
    have := hp.eq_two_or_odd
    omega
  have hkn : k < p := by omega
  refine ⟨306 * k, 306 * p, 306 * p * k, by omega, by omega, ?_, ?_⟩
  · nlinarith
  · have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hpkq : (p : ℚ) + 1 = 1223 * (k : ℚ) := by exact_mod_cast hpk
    push_cast
    field_simp
    nlinarith
