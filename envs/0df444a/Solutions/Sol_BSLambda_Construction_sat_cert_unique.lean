-- Prove2me | solution 1 for BSLambda.Construction.sat_cert_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:40.453721+00:00
-- url     : https://prove2.me/submissions/d3678635-839b-421b-92fb-d14db7e25f90

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Theorems.Thm_BSLambda_Construction_exists_conflict_of_ne
public import Theorems.Thm_BSLambda_PartialAssign_sat_unique_of_conflict


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}
namespace BSLambda.Construction
theorem _root_.solution (hT : IsTournament Arc)
    {x : Input (Coord ι r)} (hi : (cert Arc γ i).Sat x) (hj : (cert Arc γ j).Sat x) :
    i = j :=
  PartialAssign.sat_unique_of_conflict (fun _ _ hne ↦ exists_conflict_of_ne hT hne) hi hj
end BSLambda.Construction
