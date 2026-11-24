-- Prove2me | solution 1 for BSLambda.CertFamily.ind_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:14:27.816312+00:00
-- url     : https://prove2.me/submissions/0609680b-ad66-46ac-9d94-8e675b890cea

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_false_iff



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x : Input V} : F.ind x = false ↔ ∀ i, ¬ (F.P i).Sat x :=
  PartialAssign.indUnion_eq_false_iff
end BSLambda.CertFamily
