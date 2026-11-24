-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappa_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:13.698375+00:00
-- url     : https://prove2.me/submissions/e59b4de8-7406-45ec-9603-ea574c9700d8

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
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
    (c : ℂ) (F : Pkappa d kappa) :
    evalPkappa kappa (c • F) = fun z => c * evalPkappa kappa F z := by
  let _ := hd
  ext z
  by_cases hc : c = 0
  · subst c
    simp [evalPkappa]
  · unfold evalPkappa
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq hc, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    rw [Finsupp.smul_apply]
    simp [mul_left_comm, mul_comm]
end DimdPolyLEAN
