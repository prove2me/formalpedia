-- Prove2me | solution 1 for CircuitComplexity.CompileAON.oOffset_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:51.019325+00:00
-- url     : https://prove2.me/submissions/9bfb3bad-ec3a-4389-96bf-81324eec1590

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_AON
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Simulation

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.CompileAON
variable {N M G : Nat} [NeZero N] [NeZero M]
namespace CircuitComplexity.CompileAON
theorem _root_.solution (c : Circuit Basis.unboundedAON N M G) {j : Nat} (hj : j < M) :
    oOffset c (j + 1) = oOffset c j + chainLen (c.outputs ⟨j, hj⟩).fanIn := by
  unfold oOffset; rw [prefixSum_succ, oChainF_eq c hj]; omega
end CircuitComplexity.CompileAON
