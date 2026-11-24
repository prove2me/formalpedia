-- Prove2me | solution 1 for BSLambda.CertFamily.owner_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:14:27.326243+00:00
-- url     : https://prove2.me/submissions/b4aa7440-07cf-4dc2-916c-7d3b05948256

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
theorem _root_.solution (x : Ones F.ind) : (F.P (F.owner x)).Sat x.1 :=
  (F.ind_eq_true_iff.1 x.2).choose_spec
end BSLambda.CertFamily
