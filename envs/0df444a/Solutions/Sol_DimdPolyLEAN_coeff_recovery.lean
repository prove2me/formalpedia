-- Prove2me | solution 1 for DimdPolyLEAN.coeff_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:33.693407+00:00
-- url     : https://prove2.me/submissions/c9f1da51-a703-4ecb-ae55-ac5805ba4bf7

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_finite_coeff_recovery
public import Theorems.Thm_DimdPolyLEAN_toL2_eq_boxLimit
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
    (beta : Idx d) :
    coeffSkappa U beta = inner ℂ (PhiL2 kappa beta) (toL2 kappa U) := by
  let _ := hd
  let Φ : L2Tensor d := PhiL2 kappa beta
  have hlimL2 := (toL2_eq_boxLimit hd kappa U).1
  have hinner_cont : Continuous (fun F : L2Tensor d => inner ℂ Φ F) := by fun_prop
  have hlim_inner :=
    hinner_cont.continuousAt.tendsto.comp hlimL2
  have hbeta_eventually :
      ∀ᶠ J : MultiIndex d in Filter.atTop, beta ∈ box J := by
    filter_upwards [Filter.eventually_atTop.2 ⟨beta, fun J hJ => hJ⟩] with J hJ
    rw [box, Fintype.mem_piFinset]
    intro q
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hJ q)
  have hseq_coeff :
      ∀ᶠ J : MultiIndex d in Filter.atTop,
        inner ℂ Φ (evalPkappaL2 kappa (truncateFinset (box J) U)) =
          coeffSkappa U beta := by
    filter_upwards [hbeta_eventually] with J hbetaJ
    calc
      inner ℂ Φ (evalPkappaL2 kappa (truncateFinset (box J) U))
          = coeffPkappa (truncateFinset (box J) U) beta := by
            exact (finite_coeff_recovery hd kappa (truncateFinset (box J) U) beta).symm
      _ = coeffSkappa U beta := by
            simp only [coeffPkappa, coeffSkappa, truncateFinset]
            rw [Finsupp.finsetSum_apply, Finset.sum_eq_single beta]
            · simp
            · simp_all
            · simp_all
  have hlim_coeff :=
    tendsto_nhds_of_eventually_eq hseq_coeff
  exact (tendsto_nhds_unique hlim_inner hlim_coeff).symm
end DimdPolyLEAN
