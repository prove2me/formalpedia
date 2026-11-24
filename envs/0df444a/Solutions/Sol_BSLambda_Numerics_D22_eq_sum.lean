-- Prove2me | solution 1 for BSLambda.Numerics.D22_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:30:03.736017+00:00
-- url     : https://prove2.me/submissions/eb9f558e-2889-4bc2-a1e5-f175c12b4432

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Theorems.Thm_BSLambda_Numerics_depSumTwoTwo_eq


set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution :
    D22 = (∑ s ∈ Finset.Icc 2 9, Nat.choose 9 s * Nat.choose 14002 (9 - s)) - 1 :=
  depSumTwoTwo_eq.symm
end BSLambda.Numerics
