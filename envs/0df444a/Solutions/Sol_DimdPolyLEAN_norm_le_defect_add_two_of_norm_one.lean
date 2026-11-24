-- Prove2me | solution 1 for DimdPolyLEAN.norm_le_defect_add_two_of_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:35.714237+00:00
-- url     : https://prove2.me/submissions/6efc22c6-74d6-49a1-985e-8cec9d9aea5e

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseAnnulusEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private theorem evalPkappa_add_apply_wip
    {d : Nat} (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (z : Cd d) :
    evalPkappa kappa (F + G) z = evalPkappa kappa F z + evalPkappa kappa G z := by
  unfold evalPkappa
  rw [Finsupp.sum_add_index'] <;> simp [add_mul]
private lemma continuous_evalPkappa_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Continuous (evalPkappa kappa F) := by
  exact continuous_evalPkappa kappa F
private lemma continuous_defectFunctionPkappa_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    Continuous (defectFunctionPkappa_coeff_wip kappa F G) := by
  unfold defectFunctionPkappa_coeff_wip
  exact (((continuous_evalPkappa_coeff_wip kappa (F + G)).norm.sub
    (continuous_evalPkappa_coeff_wip kappa F).norm).abs)
private theorem integrable_evalPkappa_sq_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.Integrable
      (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) := by
  exact integrable_evalPkappa_sq hd kappa F
private theorem gaussianL2Norm_eq_lpNorm_coeff_wip
    {d : Nat} {α : Type*} [NormedAddCommGroup α]
     (F : Cd d -> α)
    (hF : MeasureTheory.AEStronglyMeasurable F (gammaD d)) :
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      MeasureTheory.lpNorm F 2 (gammaD d) := by
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := gammaD d) (p := (2 : NNReal)) (f := F) htwo hF
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      MeasureTheory.lpNorm F (↑(2 : NNReal)) (gammaD d)
  rw [hlp]
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) ^ ((2 : ℝ)⁻¹)
  rw [Real.sqrt_eq_rpow]
  norm_num
private theorem memLp_two_evalPkappa_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.MemLp (evalPkappa kappa F) 2 (gammaD d) := by
  exact memLp_two_evalPkappa hd kappa F
private theorem evalPkappa_lpNorm_eq_norm_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d) = ‖F‖ := by
  have hpow :
      (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ (2 : ℝ) ∂ gammaD d) =
        ∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d := by
    simp_all
  calc
    MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d)
        = Real.sqrt
            (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ (2 : ℝ) ∂ gammaD d) := by
          symm
          exact gaussianL2Norm_eq_lpNorm_coeff_wip (evalPkappa kappa F)
            (memLp_two_evalPkappa_coeff_wip hd kappa F).aestronglyMeasurable
    _ = Real.sqrt
          (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) := by rw [hpow]
    _ = ‖F‖ := by
          rw [evalPkappa_total_mass hd kappa F, Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (Real.sqrt_nonneg _)
private theorem memLp_two_defectFunctionPkappa_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    MeasureTheory.MemLp (defectFunctionPkappa_coeff_wip kappa F G) 2 (gammaD d) := by
  let _ := hd
  have hmeas :
      MeasureTheory.AEStronglyMeasurable (defectFunctionPkappa_coeff_wip kappa F G) (gammaD d) :=
    (continuous_defectFunctionPkappa_coeff_wip kappa F G).stronglyMeasurable.aestronglyMeasurable
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hplus_int :
      MeasureTheory.Integrable
        (fun z : Cd d => 2 * ‖evalPkappa kappa (F + G) z‖ ^ 2) (gammaD d) :=
    (integrable_evalPkappa_sq_coeff_wip hd kappa (F + G)).const_mul 2
  have hbase_int :
      MeasureTheory.Integrable
        (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) :=
    (integrable_evalPkappa_sq_coeff_wip hd kappa F).const_mul 2
  have hsq := hplus_int.add hbase_int
  have hmeasSq :
      MeasureTheory.AEStronglyMeasurable
        (fun z : Cd d => defectFunctionPkappa_coeff_wip kappa F G z ^ 2) (gammaD d) :=
    (continuous_defectFunctionPkappa_coeff_wip kappa F G).pow 2
      |>.stronglyMeasurable.aestronglyMeasurable
  have hbound :
      ∀ᵐ z ∂ gammaD d,
        ‖defectFunctionPkappa_coeff_wip kappa F G z ^ 2‖ <=
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
    filter_upwards with z
    have hsqz :
        defectFunctionPkappa_coeff_wip kappa F G z ^ 2 <=
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
      unfold defectFunctionPkappa_coeff_wip
      have : (‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖) ^ 2 <=
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
        linarith only [sq_nonneg (‖evalPkappa kappa (F + G) z‖ + ‖evalPkappa kappa F z‖)]
      simpa [sq_abs] using this
    simp_all
  simpa [Real.norm_eq_abs, abs_of_nonneg] using
    MeasureTheory.Integrable.mono' hsq hmeasSq hbound
private theorem defect_lpNorm_eq_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    defect F G =
      MeasureTheory.lpNorm (defectFunctionPkappa_coeff_wip kappa F G) 2 (gammaD d) := by
  let _ := hd
  simpa [defect, defectFunctionPkappa_coeff_wip, Real.norm_eq_abs, sq_abs] using
    gaussianL2Norm_eq_lpNorm_coeff_wip (defectFunctionPkappa_coeff_wip kappa F G)
      (memLp_two_defectFunctionPkappa_coeff_wip hd kappa F G).aestronglyMeasurable
private lemma evalPkappa_pointwise_bound_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) (z : Cd d) :
    ‖evalPkappa kappa G z‖ ≤
      defectFunctionPkappa_coeff_wip kappa F G z + 2 * ‖evalPkappa kappa F z‖ := by
  have hsub :
      evalPkappa kappa G z = evalPkappa kappa (F + G) z - evalPkappa kappa F z := by
    rw [evalPkappa_add_apply_wip kappa F G z, add_sub_cancel_left]
  have haux :
      ‖evalPkappa kappa (F + G) z‖ ≤
        defectFunctionPkappa_coeff_wip kappa F G z + ‖evalPkappa kappa F z‖ := by
    unfold defectFunctionPkappa_coeff_wip
    exact sub_le_iff_le_add.mp (le_abs_self _)
  calc
    ‖evalPkappa kappa G z‖ = ‖evalPkappa kappa (F + G) z - evalPkappa kappa F z‖ := by rw [hsub]
    _ ≤ ‖evalPkappa kappa (F + G) z‖ + ‖evalPkappa kappa F z‖ := norm_sub_le _ _
    _ ≤ defectFunctionPkappa_coeff_wip kappa F G z +
          ‖evalPkappa kappa F z‖ + ‖evalPkappa kappa F z‖ := by linarith only [haux]
    _ = defectFunctionPkappa_coeff_wip kappa F G z + 2 * ‖evalPkappa kappa F z‖ := by ring
private theorem norm_le_defect_add_two_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ‖G‖ ≤ defect F G + 2 := by
  have hdef_mem := memLp_two_defectFunctionPkappa_coeff_wip hd kappa F G
  have htwoF_mem :
      MeasureTheory.MemLp (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) 2 (gammaD d) :=
    (memLp_two_evalPkappa_coeff_wip hd kappa F).norm.const_smul (2 : ℝ)
  have hsum_mem := hdef_mem.add htwoF_mem
  have hmono :
      MeasureTheory.lpNorm (evalPkappa kappa G) 2 (gammaD d) ≤
        MeasureTheory.lpNorm
          (defectFunctionPkappa_coeff_wip kappa F G +
            fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d) := by
    refine MeasureTheory.lpNorm_mono_real hsum_mem ?_
    intro z
    simpa using evalPkappa_pointwise_bound_coeff_wip kappa F G z
  have htri :
      MeasureTheory.lpNorm
          (defectFunctionPkappa_coeff_wip kappa F G +
            fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d)
        ≤ MeasureTheory.lpNorm (defectFunctionPkappa_coeff_wip kappa F G) 2 (gammaD d) +
            MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) 2
              (gammaD d) := MeasureTheory.lpNorm_add_le hdef_mem
      (g := fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) (by norm_num)
  have hnormEq :
      MeasureTheory.lpNorm (fun z : Cd d => ‖evalPkappa kappa F z‖) 2 (gammaD d) =
        MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d) := by
    simpa using
      (MeasureTheory.lpNorm_norm (μ := gammaD d) (p := (2 : ENNReal))
        (memLp_two_evalPkappa_coeff_wip hd kappa F).aestronglyMeasurable)
  have htwoF_norm :
      MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
        2 (gammaD d) = 2 := by
    calc
      MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d)
          = MeasureTheory.lpNorm
              ((2 : ℝ) • fun z : Cd d => ‖evalPkappa kappa F z‖) 2 (gammaD d) := by rfl
      _ = ‖(2 : ℝ)‖ *
            MeasureTheory.lpNorm (fun z : Cd d => ‖evalPkappa kappa F z‖) 2
              (gammaD d) := by
            rw [MeasureTheory.lpNorm_const_smul]
            norm_num
      _ = 2 * MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d) := by
            simp_all
      _ = 2 * ‖F‖ := by rw [evalPkappa_lpNorm_eq_norm_coeff_wip hd kappa F]
      _ = 2 := by simp [hF_norm]
  calc
    ‖G‖ = MeasureTheory.lpNorm (evalPkappa kappa G) 2 (gammaD d) := by
          symm
          exact evalPkappa_lpNorm_eq_norm_coeff_wip hd kappa G
    _ ≤ MeasureTheory.lpNorm
          (defectFunctionPkappa_coeff_wip kappa F G +
            fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d) := hmono
    _ ≤ MeasureTheory.lpNorm (defectFunctionPkappa_coeff_wip kappa F G) 2 (gammaD d) +
          MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) 2
            (gammaD d) := htri
    _ = defect F G + 2 := by rw [← defect_lpNorm_eq_coeff_wip hd kappa F G, htwoF_norm]
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ‖G‖ ≤ defect F G + 2 :=
  norm_le_defect_add_two_coeff_wip hd kappa F G hF_norm
end DimdPolyLEAN
