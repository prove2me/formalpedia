-- Prove2me | solution 1 for BSLambda.CertFamily.owner_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:28.614321+00:00
-- url     : https://prove2.me/submissions/ffaf156f-600c-4321-9449-8fb7f6122c68

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Theorems.Thm_BSLambda_CertFamily_sat_unique
public import Theorems.Thm_BSLambda_CertFamily_owner_sat

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x : Ones F.ind} {i : ι} (h : (F.P i).Sat x.1) : F.owner x = i :=
  F.sat_unique (F.owner_sat x) h
end BSLambda.CertFamily
