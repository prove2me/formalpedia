-- Prove2me | solution 1 for BSLambda.LLL.missArcs_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:31.283103+00:00
-- url     : https://prove2.me/submissions/43bda3cd-1db3-406f-870c-3f73f1fd6d22

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
theorem _root_.solution : missArcs Arc γ Z T ⊆ arcSet Arc T := Finset.filter_subset _ _
end BSLambda.LLL
