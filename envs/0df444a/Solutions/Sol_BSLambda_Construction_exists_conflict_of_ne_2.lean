-- Prove2me | solution 2 for BSLambda.Construction.exists_conflict_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:07:15.069567+00:00
-- url     : https://prove2.me/submissions/e3e1cefe-f787-4f5e-b38e-71a45a47fbad

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Theorems.Thm_BSLambda_Construction_conflict_gateCoord
public import Theorems.Thm_BSLambda_IsTournament_arc_or_arc
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}
namespace BSLambda.Construction
theorem _root_.solution (hT : IsTournament Arc) (hij : i ≠ j) :
    ∃ v : Coord ι r, (cert Arc γ i).Conflict (cert Arc γ j) v :=
  (hT.arc_or_arc hij).elim (fun h ↦ ⟨_, conflict_gateCoord hij.symm h⟩)
    fun h ↦ ⟨_, (conflict_gateCoord hij h).symm⟩
end BSLambda.Construction
