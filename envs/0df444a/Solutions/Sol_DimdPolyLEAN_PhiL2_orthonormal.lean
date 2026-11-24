-- Prove2me | solution 1 for DimdPolyLEAN.PhiL2_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:24.638378+00:00
-- url     : https://prove2.me/submissions/f26a8ec6-b66b-44ef-afa3-dd71d5d05075

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_eq_toLp
public import Theorems.Thm_Hermite1DimdLEAN_productBasisOrthonormal
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (alpha beta : Idx d) :
    inner ℂ (PhiL2 kappa alpha) (PhiL2 kappa beta) =
      if alpha = beta then (1 : ℂ) else 0 := by
  rw [PhiL2, PhiL2, evalPkappaL2_eq_toLp hd kappa (Finsupp.single alpha 1),
    evalPkappaL2_eq_toLp hd kappa (Finsupp.single beta 1), MeasureTheory.L2.inner_def]
  have hcoe_alpha :=
    (memLp_two_evalPkappa hd kappa (Finsupp.single alpha 1)).coeFn_toLp
  have hcoe_beta :=
    (memLp_two_evalPkappa hd kappa (Finsupp.single beta 1)).coeFn_toLp
  trans ∫ z : Cd d, Phi kappa beta z * star (Phi kappa alpha z) ∂ gammaD d
  · apply MeasureTheory.integral_congr_ae
    filter_upwards [hcoe_alpha, hcoe_beta] with z hα hβ
    rw [hα, hβ]
    simp [evalPkappa, mul_comm]
  · have horth :=
      Hermite1DimdLEAN.productBasisOrthonormal (κ := kappa) (α := beta) (β := alpha)
    simp only [Hermite1DimdLEAN.gaussianInner] at horth
    simp only [Phi_eq_PhiKappaAlpha]
    rw [show (if alpha = beta then (1 : ℂ) else 0) = if beta = alpha then 1 else 0 from
      if_congr eq_comm rfl rfl]
    exact horth
end DimdPolyLEAN
