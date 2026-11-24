-- Prove2me | solution 1 for BSLambda.Numerics.D12_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:31.473805+00:00
-- url     : https://prove2.me/submissions/76714846-6347-4ffe-846f-8fc59a48142e

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Theorems.Thm_BSLambda_Numerics_depSumOneTwo_eq


set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution :
    D12 = ∑ s ∈ Finset.Icc 2 5, Nat.choose 5 s * Nat.choose 14006 (9 - s) := depSumOneTwo_eq.symm
end BSLambda.Numerics
