-- Prove2me | solution 1 for BSLambda.Construction.one_le_dist_cert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:17.315633+00:00
-- url     : https://prove2.me/submissions/98ee0ed2-4624-4c5a-b6d4-418283e90c41

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Theorems.Thm_BSLambda_Construction_exists_conflict_of_ne
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
theorem _root_.solution (hT : IsTournament Arc) (hij : i ≠ j)
    {x : Input (Coord ι r)} (hx : (cert Arc γ i).Sat x) : 1 ≤ (cert Arc γ j).dist x :=
  (exists_conflict_of_ne hT hij).elim fun v hv ↦ Finset.card_pos.2 ⟨v, hv.mem_violSet hx⟩
end BSLambda.Construction
