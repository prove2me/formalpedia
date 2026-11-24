-- Prove2me | solution 1 for BSLambda.LLL.mem_discSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:59:57.974879+00:00
-- url     : https://prove2.me/submissions/5bdca5cc-d659-4bde-b3a5-0b1a3dd6a15a

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
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} {T : Finset ι}
  {p : ι × ι}
omit [DecidableEq ι]
namespace BSLambda.LLL
theorem _root_.solution {h j : ι} : j ∈ discSet γ Z T h ↔ j ∈ T ∧ ¬ (Z j ⊆ {γ h j}) :=
  Finset.mem_filter
end BSLambda.LLL
