-- Prove2me | solution 1 for BSLambda.CertFamily.conflict_conflictCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:14:32.787045+00:00
-- url     : https://prove2.me/submissions/78189719-99bc-42f5-8e41-b0f94abcb979

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {i j : ι} (h : i ≠ j) : (F.P i).Conflict (F.P j) (F.conflictCoord h) :=
  (F.uniqueConflict i j h).choose_spec.1
end BSLambda.CertFamily
