-- Prove2me | solution 1 for BSLambda.LLL.not_close_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:22.346659+00:00
-- url     : https://prove2.me/submissions/bfae5048-3447-4785-9b00-f1705c41d2cd

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_not_intObstruction_nine
public import Theorems.Thm_BSLambda_LLL_intObstruction_of_close


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (hT : IsTournament Arc) {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) {S : Finset ι} (hS : S.card = 9)
    {h : ι} (hh : h ∈ S) {x : Input (Coord ι r)}
    (hx : (cert Arc (toGamma ω) h).Sat x)
    (hclose : ∀ i ∈ S, i ≠ h → (cert Arc (toGamma ω) i).dist x ≤ 2) : False :=
  not_intObstruction_nine hgood hS hh (intObstruction_of_close hT hx hclose)
end BSLambda.LLL
