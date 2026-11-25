-- Prove2me | solution 1 for Erdos679.cardDistinctFactors_primeProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:31:36.21686+00:00
-- url     : https://prove2.me/submissions/3a199744-b785-46cb-bd92-188ca5443bdd

module
public import Definitions.Def_Erdos679_StirlingBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_Analytic
public import Theorems.Thm_Erdos679_primeFactors_primeProduct

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (m : ℕ) :
    ArithmeticFunction.cardDistinctFactors (primeProduct m) = m := by
  have hcard : (primeProduct m).primeFactors.card = m := by
    rw [primeFactors_primeProduct,
      Finset.card_image_of_injective _ (Nat.nth_injective Nat.infinite_setOfPred_prime),
      Finset.card_range]
  simpa only [← Nat.toFinset_factors, List.card_toFinset,
    ArithmeticFunction.cardDistinctFactors_apply] using hcard
end Erdos679
