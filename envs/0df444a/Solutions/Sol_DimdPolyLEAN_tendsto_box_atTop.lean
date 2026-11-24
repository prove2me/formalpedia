-- Prove2me | solution 1 for DimdPolyLEAN.tendsto_box_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:11.80182+00:00
-- url     : https://prove2.me/submissions/856a79d4-911d-45f0-a693-566c96ae33da

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_box_subset_box
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
    {d : Nat} :
    Filter.Tendsto (fun J : MultiIndex d => box J) Filter.atTop Filter.atTop := by
  refine (show Monotone (fun J : MultiIndex d => box J) from ?_).tendsto_atTop_finset ?_
  · intro J K hJK
    exact box_subset_box hJK
  · intro alpha
    refine ⟨alpha, ?_⟩
    rw [box, Fintype.mem_piFinset]
    simp_all
end DimdPolyLEAN
