-- Prove2me | solution 1 for Freiman.middle_finite_exception_support
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:47:35.269306+00:00
-- url     : https://prove2.me/submissions/d9eb2ed4-bd14-4c06-b28d-50c13ad715e5

import Definitions.Def_Freiman_middleRoots
import Mathlib.Tactic.Linarith
open Freiman
set_option autoImplicit false

theorem solution :
    ∀ (c : MiddleCore) (a : ℤ→ℕ+), middleCompatible c a → ∃ N : ℕ, ∀ i : ℤ, N ≤ i.natAbs → (a i:ℕ) ≤ 3 := by
  intro c a h
  refine ⟨c.left.length + c.right.length + 1, ?_⟩
  intro i hi
  rcases h with ⟨h0, hl, hr, hlt, hrt⟩
  by_cases hs : 0 ≤ i
  · have hpos : 0 < i := by omega
    have hin : ((i.toNat - 1 : ℕ) : ℤ) + 1 = i := by omega
    have hh := hrt (i.toNat - 1) (by omega)
    simpa only [hin] using hh
  · have hin : -(((-i).toNat - 1 : ℕ) : ℤ) - 1 = i := by omega
    have hh := hlt ((-i).toNat - 1) (by omega)
    simpa only [hin] using hh
#print axioms solution
