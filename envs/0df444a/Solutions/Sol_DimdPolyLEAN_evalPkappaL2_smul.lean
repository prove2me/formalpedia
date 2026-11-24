-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappaL2_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:45.385101+00:00
-- url     : https://prove2.me/submissions/b58c5f0a-2df1-4ce4-bb0f-76b4a1b591bd

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_smul
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_eq_toLp

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
    evalPkappaL2 kappa (c • F) = c • evalPkappaL2 kappa F := by
  let hF := memLp_two_evalPkappa hd kappa F
  rw [evalPkappaL2_eq_toLp hd kappa (c • F)]
  calc
    (memLp_two_evalPkappa hd kappa (c • F)).toLp (evalPkappa kappa (c • F))
        = (hF.const_smul c).toLp (c • evalPkappa kappa F) := by
          apply MeasureTheory.MemLp.toLp_congr
          exact Filter.Eventually.of_forall fun z => by
            rw [congrFun (evalPkappa_smul hd kappa c F) z]
            rfl
    _ = c • hF.toLp (evalPkappa kappa F) := hF.toLp_const_smul c
    _ = c • evalPkappaL2 kappa F := by rw [← evalPkappaL2_eq_toLp hd kappa F]
end DimdPolyLEAN
