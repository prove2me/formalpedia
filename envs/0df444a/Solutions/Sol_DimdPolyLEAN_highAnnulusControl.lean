-- Prove2me | solution 1 for DimdPolyLEAN.highAnnulusControl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:10.061265+00:00
-- url     : https://prove2.me/submissions/5007ebbc-079c-4d4c-8716-42bb9f58e1ab

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseCircleEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductAnnulusCircle
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseAnnulusEstimate
public import Theorems.Thm_DimdPolyLEAN_finite_base_annulus_estimate
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1) :
    ∃ J : Nat, ∃ delta_high : ℝ, 0 < delta_high ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        defect F (t • H) <= delta_high * t ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by
  let _ := hd
  obtain ⟨J, C, hC_pos, hann⟩ :=
    finite_base_annulus_estimate hd kappa F ⟨hF_ne, hF_norm⟩ (1 / 8) (by norm_num)
  let delta_high : ℝ := min 1 (1 / (8 * C))
  have hdelta_high_pos : 0 < delta_high := by
    dsimp [delta_high]
    exact lt_min zero_lt_one (one_div_pos.mpr (mul_pos (by norm_num) hC_pos))
  refine ⟨J, delta_high, hdelta_high_pos, ?_⟩
  intro H t horth hH_norm ht_pos ht_le_four hdefect
  let _ := horth
  have hdelta_nonneg : 0 <= delta_high := le_of_lt hdelta_high_pos
  have hdelta_le_one : delta_high <= 1 := by
    dsimp [delta_high]
    exact min_le_left _ _
  have hdelta_le_inv : delta_high <= 1 / (8 * C) := by
    dsimp [delta_high]
    exact min_le_right _ _
  have hCdelta_le : C * delta_high <= 1 / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hdelta_le_inv (le_of_lt hC_pos)
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    simp_all
  have hdelta_sq_le : delta_high ^ 2 <= delta_high := by
    nlinarith only [
      hdelta_high_pos, hdelta_le_one, sq_nonneg delta_high
    ]
  have hCdelta_sq_le : C * delta_high ^ 2 <= 1 / 8 := by
    calc
      C * delta_high ^ 2 <= C * delta_high :=
        mul_le_mul_of_nonneg_left hdelta_sq_le (le_of_lt hC_pos)
      _ <= 1 / 8 := hCdelta_le
  have hhigh :
      highAnnulusMass J (ofPkappa kappa H) <= C * delta_high ^ 2 + 1 / 8 :=
    hann hH_norm ht_pos ht_le_four hdelta_nonneg hdefect
  linarith only [hCdelta_sq_le, hhigh]
end DimdPolyLEAN
