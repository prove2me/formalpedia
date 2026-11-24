-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappaL2_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:41.852363+00:00
-- url     : https://prove2.me/submissions/5c4635d6-2c0e-4ce3-bfc1-96d19abe5232

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_add
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
    (F G : Pkappa d kappa) :
    evalPkappaL2 kappa (F + G) = evalPkappaL2 kappa F + evalPkappaL2 kappa G := by
  let hF := memLp_two_evalPkappa hd kappa F
  let hG := memLp_two_evalPkappa hd kappa G
  rw [evalPkappaL2_eq_toLp hd kappa (F + G)]
  calc
    (memLp_two_evalPkappa hd kappa (F + G)).toLp (evalPkappa kappa (F + G))
        = (hF.add hG).toLp (evalPkappa kappa F + evalPkappa kappa G) := by
          apply MeasureTheory.MemLp.toLp_congr
          exact Filter.Eventually.of_forall fun z => by
            rw [congrFun (evalPkappa_add hd kappa F G) z]
            rfl
    _ = hF.toLp (evalPkappa kappa F) + hG.toLp (evalPkappa kappa G) :=
          hF.toLp_add hG
    _ = evalPkappaL2 kappa F + evalPkappaL2 kappa G := by
          rw [← evalPkappaL2_eq_toLp hd kappa F, ← evalPkappaL2_eq_toLp hd kappa G]
end DimdPolyLEAN
