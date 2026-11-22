-- Prove2me | solution 1 for CircuitComplexity.DNF.xorBool_complexity_lb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:22.54628+00:00
-- url     : https://prove2.me/submissions/595a3cf5-c69b-470b-a863-3e612bfe4451

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
public import Definitions.Def_LeanPool_CircuitComplexity_NF
public import Theorems.Thm_CircuitComplexity_DNF_flip_complexity_lb
public import Theorems.Thm_CircuitComplexity_Schnorr_xorBool_flip


set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
namespace DNF
theorem _root_.solution (φ : DNF N) (hN : 1 ≤ N)
    (hcomp : ∀ x, φ.eval x = Schnorr.xorBool N x) :
    2 ^ (N - 1) ≤ φ.complexity := by
  exact φ.flip_complexity_lb hN (Schnorr.xorBool N) hcomp
    (fun x i => Schnorr.xorBool_flip N x i)
end DNF
end CircuitComplexity
