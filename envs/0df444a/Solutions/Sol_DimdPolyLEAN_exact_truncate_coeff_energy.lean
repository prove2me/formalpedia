-- Prove2me | solution 1 for DimdPolyLEAN.exact_truncate_coeff_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:26.291216+00:00
-- url     : https://prove2.me/submissions/ec2b3a0d-3d9c-4d95-87b4-3208092f66f1

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
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (E : Finset (Idx d)) (F : Skappa d kappa) :
    ‖truncateFinset E F‖ ^ 2 = Finset.sum E (fun alpha => ‖coeffSkappa F alpha‖ ^ 2) := by
  let _ := hd
  classical
  have hcoeff :
      ∀ alpha : Idx d, truncateFinset E F alpha = if alpha ∈ E then coeffSkappa F alpha else 0 := by
    intro alpha
    have hsum :
        truncateFinset E F alpha =
          (∑ beta ∈ E, Finsupp.single beta (coeffSkappa F beta)) alpha := by rfl
    rw [hsum]
    by_cases h : alpha ∈ E
    · simp [h, Finsupp.single_apply]
    · simp [h, Finsupp.single_apply]
  have hsupp : (truncateFinset E F).support ⊆ E := by
    intro alpha halpha
    simp_all
  change
    (Real.sqrt (Finset.sum (truncateFinset E F).support
      (fun alpha => ‖truncateFinset E F alpha‖ ^ 2))) ^ 2 =
      Finset.sum E (fun alpha => ‖coeffSkappa F alpha‖ ^ 2)
  rw [Real.sq_sqrt]
  · calc
      Finset.sum (truncateFinset E F).support
          (fun alpha => ‖truncateFinset E F alpha‖ ^ 2)
          = Finset.sum E (fun alpha => ‖truncateFinset E F alpha‖ ^ 2) := by
            exact Finset.sum_subset hsupp fun alpha _E hsupport => by
              simp_all
      _ = Finset.sum E (fun alpha => ‖coeffSkappa F alpha‖ ^ 2) := by
            simp_all
  · positivity
end DimdPolyLEAN
