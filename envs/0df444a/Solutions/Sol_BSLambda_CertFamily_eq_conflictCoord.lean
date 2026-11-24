-- Prove2me | solution 1 for BSLambda.CertFamily.eq_conflictCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:16:42.443668+00:00
-- url     : https://prove2.me/submissions/fd4d7de4-8468-438f-b89c-fd385b489414

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
theorem _root_.solution {i j : ι} (h : i ≠ j) {v : V} (hv : (F.P i).Conflict (F.P j) v) :
    v = F.conflictCoord h :=
  (F.uniqueConflict i j h).choose_spec.2 v hv
end BSLambda.CertFamily
