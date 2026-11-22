-- Prove2me | solution 1 for CircuitComplexity.CNF.xorBool_complexity_lb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:25.457677+00:00
-- url     : https://prove2.me/submissions/d65a0f7d-62f2-4075-86a7-6e7e2203a121

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
public import Definitions.Def_LeanPool_CircuitComplexity_NF
public import Theorems.Thm_CircuitComplexity_CNF_eval_neg
public import Theorems.Thm_CircuitComplexity_CNF_neg_complexity
public import Theorems.Thm_CircuitComplexity_DNF_eval_neg
public import Theorems.Thm_CircuitComplexity_DNF_flip_complexity_lb
public import Theorems.Thm_CircuitComplexity_Literal_eval_neg
public import Theorems.Thm_CircuitComplexity_Schnorr_xorBool_flip


set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
namespace CNF
theorem _root_.solution (φ : CNF N) (hN : 1 ≤ N)
    (hcomp : ∀ x, φ.eval x = Schnorr.xorBool N x) :
    2 ^ (N - 1) ≤ φ.complexity := by
  -- φ.neg is a DNF computing ¬xorBool, which is also flip-sensitive
  rw [← CNF.neg_complexity]
  apply DNF.flip_complexity_lb φ.neg hN (fun x => !(Schnorr.xorBool N x))
  · intro x; rw [CNF.eval_neg, hcomp]
  · intro x i
    rw [Schnorr.xorBool_flip, Bool.not_not]
end CNF
end CircuitComplexity
