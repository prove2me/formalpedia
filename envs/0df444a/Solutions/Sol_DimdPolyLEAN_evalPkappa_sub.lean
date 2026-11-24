-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappa_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:14.76833+00:00
-- url     : https://prove2.me/submissions/587671b5-8350-4926-8606-7300eb845aee

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_add
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_smul
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    evalPkappa kappa (F - G) = fun z => evalPkappa kappa F z - evalPkappa kappa G z := by
  let _ := hd
  have hneg : -G = (-1 : ℂ) • G := by
    simp_all
  rw [sub_eq_add_neg, hneg, evalPkappa_add hd kappa F ((-1 : ℂ) • G),
    evalPkappa_smul hd kappa (-1 : ℂ) G]
  ext z
  simp [sub_eq_add_neg]
end DimdPolyLEAN
