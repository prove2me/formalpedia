-- Prove2me | solution 1 for BSLambda.Construction.gateCoord_mem_violSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:06.741308+00:00
-- url     : https://prove2.me/submissions/e18cc18b-f019-47b6-8ef5-748fc25da8c3

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Theorems.Thm_BSLambda_Construction_conflict_gateCoord
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
attribute [local simp] BSLambda.PartialAssign.mem_violSet



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}
namespace BSLambda.Construction
theorem _root_.solution (hji : j ≠ i) (hij : Arc i j)
    {x : Input (Coord ι r)} (hx : (cert Arc γ i).Sat x) :
    gateCoord γ i j ∈ (cert Arc γ j).violSet x :=
  (conflict_gateCoord hji hij).mem_violSet hx
end BSLambda.Construction
