-- Prove2me | solution 1 for BSLambda.CertFamily.sat_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:07.006892+00:00
-- url     : https://prove2.me/submissions/5f39ec90-379c-4375-a61b-45ffd93b0b33

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Theorems.Thm_BSLambda_CertFamily_conflict_conflictCoord
public import Theorems.Thm_BSLambda_PartialAssign_sat_unique_of_conflict


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {i j : ι} {x : Input V} (hi : (F.P i).Sat x) (hj : (F.P j).Sat x) : i = j :=
  PartialAssign.sat_unique_of_conflict
    (fun _ _ hij ↦ ⟨_, F.conflict_conflictCoord hij⟩) hi hj
end BSLambda.CertFamily
