-- Prove2me | solution 1 for DimdPolyLEAN.toL2_eq_of_toFun_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:06.455793+00:00
-- url     : https://prove2.me/submissions/dd177419-4958-48f5-9f27-bfd852aec837

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d} {U V : Skappa d kappa}
    (h : ∀ z, toFun kappa U z = toFun kappa V z) :
    toL2 kappa U = toL2 kappa V := by
  let _ := hd
  have hfun : toFun kappa U = toFun kappa V := funext h
  unfold toL2
  rw [hfun]
end DimdPolyLEAN
