-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappa_truncateFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:17.936588+00:00
-- url     : https://prove2.me/submissions/1ce27179-7961-48c3-8de2-52f759ff4c95

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_add
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (E : Finset (Idx d)) :
    evalPkappa kappa (truncateFinset E U) =
      fun z : Cd d => ∑ alpha ∈ E, coeffSkappa U alpha * Phi kappa alpha z := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      ext z
      simp [truncateFinset, evalPkappa]
  | insert alpha E hnot hE =>
      ext z
      have hE' :
          Finsupp.sum (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta))
              (fun beta c => c * Phi kappa beta z) =
            ∑ beta ∈ E, coeffSkappa U beta * Phi kappa beta z := by
        exact congrFun hE z
      rw [show truncateFinset (insert alpha E) U =
          Finsupp.single alpha (coeffSkappa U alpha) +
            (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta)) by
        simp [truncateFinset, Finset.sum_insert hnot]]
      rw [congrFun
        (evalPkappa_add hd kappa (Finsupp.single alpha (coeffSkappa U alpha))
          (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta))) z]
      rw [Finset.sum_insert hnot]
      simp [evalPkappa, hE']
end DimdPolyLEAN
