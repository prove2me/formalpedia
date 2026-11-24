-- Prove2me | solution 1 for BSLambda.Construction.eq_gateCoord_of_mem_violSet_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:11.485645+00:00
-- url     : https://prove2.me/submissions/936fcd36-597b-4d86-9c76-b701382253fa

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Theorems.Thm_BSLambda_Construction_eq_gateCoord_of_conflict
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_Sat_eq_of_fixed
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_exists
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet_iff_exists_ne


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}
namespace BSLambda.Construction
theorem _root_.solution (hT : IsTournament Arc)
    (hji : j ≠ i) (hij : Arc i j)
    {x : Input (Coord ι r)} (hx : (cert Arc γ i).Sat x) {v : Coord ι r}
    (hv : v ∈ (cert Arc γ j).violSet x) (hfix : v ∈ (cert Arc γ i).fixedSet) :
    v = gateCoord γ i j := by
  obtain ⟨b, hb, hne⟩ := PartialAssign.mem_violSet_iff_exists_ne.1 hv
  obtain ⟨b', hb'⟩ := PartialAssign.mem_fixedSet_iff_exists.1 hfix
  rw [hx.eq_of_fixed hb'] at hne
  refine eq_gateCoord_of_conflict hT hji hij ⟨b', hb', ?_⟩
  rw [hb, Bool.eq_not_of_ne hne.symm]
end BSLambda.Construction
