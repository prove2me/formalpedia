-- Prove2me | solution 1 for BSLambda.LLL.Flag1.Active.owner_notMem_nonOwners
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:01:18.720155+00:00
-- url     : https://prove2.me/submissions/79b4f262-b521-4d5d-ad3f-28b1185e7fcf

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
open BSLambda.LLL.Flag1
omit [Fintype ι]
variable {F : Flag1 ι} {Arc : ι → ι → Bool} {a j : ι} {p : ι × ι}
open BSLambda.LLL.Flag1.Active
variable (hF : F.Active Arc)
include hF
namespace BSLambda.LLL.Flag1.Active
theorem _root_.solution : F.owner ∉ F.nonOwners := hF.1
end BSLambda.LLL.Flag1.Active
