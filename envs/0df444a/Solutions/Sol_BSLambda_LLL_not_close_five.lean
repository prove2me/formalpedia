-- Prove2me | solution 1 for BSLambda.LLL.not_close_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:35:52.758074+00:00
-- url     : https://prove2.me/submissions/cecd605e-6076-480b-ab57-8862ff09dd0a

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_not_intObstruction_five
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
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) {S : Finset ι} (hS : S.card = 5)
    {h : ι} (hh : h ∈ S) {x : Input (Coord ι r)}
    (hx : (cert Arc (toGamma ω) h).Sat x)
    (hclose : ∀ i ∈ S, i ≠ h → (cert Arc (toGamma ω) i).dist x ≤ 1) : False :=
  not_intObstruction_five hT hgood hS hh (intObstruction_of_close hT hx hclose)
end BSLambda.LLL
