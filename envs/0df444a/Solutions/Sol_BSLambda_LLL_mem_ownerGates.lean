-- Prove2me | solution 1 for BSLambda.LLL.mem_ownerGates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:59:29.887407+00:00
-- url     : https://prove2.me/submissions/da14f4ce-faed-4eba-8675-c8ded45afd52

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace BSLambda.LLL
theorem _root_.solution {i : ι} {T : Finset ι} {p : ι × ι} :
    p ∈ ownerGates i T ↔ p.1 = i ∧ p.2 ∈ T := by
  rw [ownerGates, Finset.mem_product, Finset.mem_singleton]
end BSLambda.LLL
