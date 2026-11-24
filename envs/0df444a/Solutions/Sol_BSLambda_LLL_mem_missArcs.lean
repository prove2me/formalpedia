-- Prove2me | solution 1 for BSLambda.LLL.mem_missArcs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:59:56.03962+00:00
-- url     : https://prove2.me/submissions/3a5a5e12-88a5-4044-9e97-5fa13a92373e

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
theorem _root_.solution : p ∈ missArcs Arc γ Z T ↔ p ∈ arcSet Arc T ∧ γ p.1 p.2 ∉ Z p.2 :=
  Finset.mem_filter
end BSLambda.LLL
