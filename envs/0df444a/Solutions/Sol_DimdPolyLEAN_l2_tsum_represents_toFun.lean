-- Prove2me | solution 1 for DimdPolyLEAN.l2_tsum_represents_toFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:03.332806+00:00
-- url     : https://prove2.me/submissions/10092231-0f7c-453f-84e1-dfcfdf9abdac

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_partialSum_tendsto_toFun_pointwise
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_eq_toLp
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_box_tendsto_tsum
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_truncateFinset
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsTensorL2Rep
      (∑' alpha : Idx d, coeffSkappa U alpha • PhiL2 kappa alpha)
      (toFun kappa U) := by
  classical
  let S : L2Tensor d := ∑' alpha : Idx d, coeffSkappa U alpha • PhiL2 kappa alpha
  have hL2 :
      Filter.Tendsto (fun J : MultiIndex d =>
          evalPkappaL2 kappa (truncateFinset (box J) U))
        Filter.atTop (nhds S) := by exact evalPkappaL2_box_tendsto_tsum hd kappa U
  have hInMeasure := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hL2
  obtain ⟨ns, hns, hns_ae⟩ := hInMeasure.exists_seq_tendsto_ae'
  have hpartial_ae :
      ∀ᵐ z ∂ gammaD d, ∀ n : ℕ,
        ((evalPkappaL2 kappa (truncateFinset (box (ns n)) U) : L2Tensor d) :
            Cd d -> ℂ) z =
          partialSum kappa U (ns n) z := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    have hcoe_eval :
        ((evalPkappaL2 kappa (truncateFinset (box (ns n)) U) : L2Tensor d) :
            Cd d -> ℂ) =ᵐ[gammaD d]
          evalPkappa kappa (truncateFinset (box (ns n)) U) := by
      rw [evalPkappaL2_eq_toLp hd]
      exact (memLp_two_evalPkappa hd kappa (truncateFinset (box (ns n)) U)).coeFn_toLp
    filter_upwards [hcoe_eval] with z hz
    rw [hz, congrFun (evalPkappa_truncateFinset hd kappa U (box (ns n))) z]
    rfl
  have hS_ae :
      (S : Cd d -> ℂ) =ᵐ[gammaD d] toFun kappa U := by
    filter_upwards [hns_ae, hpartial_ae] with z hSlim hpartial
    have hpartial_lim_S :
        Filter.Tendsto (fun n : ℕ => partialSum kappa U (ns n) z) Filter.atTop
          (nhds (S z)) := by
      simp_all
    have hpartial_lim_toFun :
        Filter.Tendsto (fun n : ℕ => partialSum kappa U (ns n) z) Filter.atTop
          (nhds (toFun kappa U z)) :=
      (partialSum_tendsto_toFun_pointwise kappa U z).comp hns
    exact tendsto_nhds_unique hpartial_lim_S hpartial_lim_toFun
  have hmem : MeasureTheory.MemLp (toFun kappa U) 2 (gammaD d) :=
    (MeasureTheory.memLp_congr_ae hS_ae).1 (MeasureTheory.Lp.memLp S)
  have htoLp : hmem.toLp (toFun kappa U) = S := by
    apply MeasureTheory.Lp.ext
    exact hmem.coeFn_toLp.trans hS_ae.symm
  exact ⟨hmem, by exact htoLp⟩
end DimdPolyLEAN
