-- Prove2me | solution 1 for Erdos684.primeWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:48:12.812983+00:00
-- url     : https://prove2.me/submissions/9d40cb68-3f87-42fa-87b1-23bdc870f3a6

module
public import Definitions.Def_Erdos684_Finite
public import Definitions.Def_Erdos684_BadPrimes
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Erdos684_Averaging

set_option autoImplicit false
@[expose] public section
public section
open Finset Real
open Erdos684
namespace Erdos684
theorem _root_.solution (n k p : ℕ) (hp : p.Prime) : 0 ≤ primeWeight n k p := by
  unfold primeWeight
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
  · exact le_rfl
end Erdos684
