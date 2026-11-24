-- Prove2me | solution 1 for DimdPolyLEAN.finite_base_annulus_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:39.128976+00:00
-- url     : https://prove2.me/submissions/6c6c90e8-5893-4b37-a761-b3a85c8c6c97

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
public import Theorems.Thm_DimdPolyLEAN_finite_base_product_annulus_estimate
public import Theorems.Thm_DimdPolyLEAN_annulusMassPartition
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
noncomputable section
open MeasureTheory
namespace DimdPolyLEAN
private theorem lowAnnulusMass_nonneg_wip
    {d : Nat} {kappa : MultiIndex d} (J : Nat) (F : Skappa d kappa) :
    0 <= lowAnnulusMass J F := by
  unfold lowAnnulusMass annulusMass
  refine Finset.sum_nonneg ?_
  intro j hj
  exact MeasureTheory.integral_nonneg fun z => by
    by_cases hz : z ∈ productAnnulus j <;> simp [Set.indicator, hz]
private theorem highAnnulusMass_le_norm_sq_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) (H : Pkappa d kappa) :
    highAnnulusMass J (ofPkappa kappa H) <= ‖H‖ ^ 2 := by
  linarith only [annulusMassPartition hd kappa J H,
    lowAnnulusMass_nonneg_wip J (ofPkappa kappa H)]
private theorem defect_nonneg_annulus
    {d : Nat} {kappa : MultiIndex d} (F G : Pkappa d kappa) :
    0 <= defect F G := Real.sqrt_nonneg _
private theorem toFun_ofPkappa_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa F) = evalPkappa kappa F := by
  let _ := hd
  ext z
  rw [toFun, evalPkappa, Finsupp.sum]
  have hzero :
      ∀ alpha ∉ F.support,
        coeffSkappa (ofPkappa kappa F) alpha * Phi kappa alpha z = 0 := by
    intro alpha halpha
    simp [coeffSkappa, ofPkappa, Finsupp.notMem_support_iff.mp halpha]
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [coeffSkappa, ofPkappa]
private theorem evalPkappa_smul_real_annulus
    {d : Nat} (kappa : MultiIndex d) (t : ℝ) (H : Pkappa d kappa) :
    evalPkappa kappa (t • H) = fun z => (t : ℂ) * evalPkappa kappa H z := by
  ext z
  by_cases ht : t = 0
  · subst t
    simp [evalPkappa]
  · unfold evalPkappa
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq ht, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    rw [Finsupp.smul_apply]
    change ((t : ℂ) * H alpha) * Phi kappa alpha z =
      (t : ℂ) * (H alpha * Phi kappa alpha z)
    ring
private theorem toFun_ofPkappa_smul_real_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (t : ℝ) (H : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa (t • H)) =
      fun z => (t : ℂ) * toFun kappa (ofPkappa kappa H) z := by
  rw [toFun_ofPkappa_annulus hd kappa (t • H), toFun_ofPkappa_annulus hd kappa H]
  exact evalPkappa_smul_real_annulus kappa t H
private theorem totalMass_ofPkappa_smul_real_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (t : ℝ) (H : Pkappa d kappa) :
    (∫ z, ‖toFun kappa (ofPkappa kappa (t • H)) z‖ ^ 2 ∂ gammaD d) =
      t ^ 2 * (∫ z, ‖toFun kappa (ofPkappa kappa H) z‖ ^ 2 ∂ gammaD d) := by
  rw [toFun_ofPkappa_smul_real_annulus hd kappa t H]
  have hfun :
      (fun z : Cd d => ‖(t : ℂ) * toFun kappa (ofPkappa kappa H) z‖ ^ 2) =
        fun z : Cd d => t ^ 2 * ‖toFun kappa (ofPkappa kappa H) z‖ ^ 2 := by
    ext z
    simp [Real.norm_eq_abs, sq_abs, mul_pow]
  rw [hfun, MeasureTheory.integral_const_mul]
private theorem annulusMass_ofPkappa_smul_real_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (j : Idx d) (t : ℝ) (H : Pkappa d kappa) :
    annulusMass j (ofPkappa kappa (t • H)) =
      t ^ 2 * annulusMass j (ofPkappa kappa H) := by
  unfold annulusMass
  rw [toFun_ofPkappa_smul_real_annulus hd kappa t H]
  have hfun :
      (fun z : Cd d =>
          Set.indicator (productAnnulus j)
            (fun w => ‖(t : ℂ) * toFun kappa (ofPkappa kappa H) w‖ ^ 2) z) =
        fun z : Cd d =>
          t ^ 2 * Set.indicator (productAnnulus j)
            (fun w => ‖toFun kappa (ofPkappa kappa H) w‖ ^ 2) z := by
    ext z
    by_cases hz : z ∈ productAnnulus j
    · simp [Set.indicator, hz, Real.norm_eq_abs, sq_abs, mul_pow]
    · simp [Set.indicator, hz]
  rw [hfun, MeasureTheory.integral_const_mul]
private theorem lowAnnulusMass_ofPkappa_smul_real_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) (t : ℝ) (H : Pkappa d kappa) :
    lowAnnulusMass J (ofPkappa kappa (t • H)) =
      t ^ 2 * lowAnnulusMass J (ofPkappa kappa H) := by
  unfold lowAnnulusMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact annulusMass_ofPkappa_smul_real_annulus hd kappa j t H
private theorem highAnnulusMass_ofPkappa_smul_real
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) (t : ℝ) (H : Pkappa d kappa) :
    highAnnulusMass J (ofPkappa kappa (t • H)) =
      t ^ 2 * highAnnulusMass J (ofPkappa kappa H) := by
  unfold highAnnulusMass
  rw [totalMass_ofPkappa_smul_real_annulus hd kappa t H,
    lowAnnulusMass_ofPkappa_smul_real_annulus hd kappa J t H]
  ring
private theorem norm_smul_pkappa_real_sq_annulus
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (t : ℝ) (H : Pkappa d kappa) :
    ‖t • H‖ ^ 2 = t ^ 2 * ‖H‖ ^ 2 := by
  let _ := hd
  by_cases ht : t = 0
  · subst t
    have hzero_norm : ‖(0 : Pkappa d kappa)‖ = 0 := by
      change
        Real.sqrt
          (Finset.sum (0 : Pkappa d kappa).support
            (fun alpha => ‖(0 : Pkappa d kappa) alpha‖ ^ 2)) = 0
      simp
    simp [hzero_norm]
  · change
      (Real.sqrt (Finset.sum (t • H).support (fun alpha => ‖(t • H) alpha‖ ^ 2))) ^ 2 =
        t ^ 2 * (Real.sqrt (Finset.sum H.support (fun alpha => ‖H alpha‖ ^ 2))) ^ 2
    rw [Finsupp.support_smul_eq ht]
    have hsum :
        Finset.sum H.support (fun alpha => ‖(t • H) alpha‖ ^ 2) =
          t ^ 2 * Finset.sum H.support (fun alpha => ‖H alpha‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro alpha halpha
      simp [Finsupp.smul_apply, Real.norm_eq_abs, sq_abs, mul_pow]
    rw [hsum, Real.sq_sqrt (mul_nonneg (sq_nonneg t) (by positivity)), Real.sq_sqrt (by positivity)]
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF : basePointNormalized F) :
    ∀ eps : ℝ, 0 < eps ->
      ∃ J : Nat, ∃ C : ℝ, 0 < C ∧
        ∀ {H : Pkappa d kappa} {t eta : ℝ},
          ‖H‖ = 1 ->
          0 < t ->
          t <= 4 ->
          0 <= eta ->
          defect F (t • H) <= eta * t ->
          highAnnulusMass J (ofPkappa kappa H) <= C * eta ^ 2 + eps := by
  let _ := hd
  /-
  Scaffolding contract:
  normalized finite-shell form of the product-annulus estimate. The scalar
  `eta` is an explicit upper bound for the divided defect `defect F (t • H) / t`.
  Completion, subsequences, and shell extraction remain hidden behind this
  finite theorem.
  -/
  intro eps h_eps
  by_cases heps_large : 1 <= eps
  · refine ⟨0, 1, by norm_num, ?_⟩
    intro H t eta hH_norm ht_pos ht_le_four heta_nonneg hdefect
    have hhigh_le : highAnnulusMass 0 (ofPkappa kappa H) <= ‖H‖ ^ 2 :=
      highAnnulusMass_le_norm_sq_wip hd kappa 0 H
    have hH_sq : ‖H‖ ^ 2 = 1 := by nlinarith only [hH_norm]
    linarith only [heps_large, hhigh_le, hH_sq, sq_nonneg eta]
  · obtain ⟨J, M, hM, C, hC_pos, hann⟩ :=
      finite_base_product_annulus_estimate hd kappa F hF eps h_eps
    refine ⟨J, C, hC_pos, ?_⟩
    intro H t eta hH_norm ht_pos ht_le_four heta_nonneg hdefect
    have hprod := hann (t • H)
    rw [highAnnulusMass_ofPkappa_smul_real hd kappa J t H,
      norm_smul_pkappa_real_sq_annulus hd t H] at hprod
    have ht_sq_pos : 0 < t ^ 2 := by positivity
    have hH_sq : ‖H‖ ^ 2 = 1 := by nlinarith only [h_eps, heps_large, hH_norm]
    have hdef_nonneg : 0 <= defect F (t • H) := defect_nonneg_annulus F (t • H)
    have hdef_sq : defect F (t • H) ^ 2 <= (eta * t) ^ 2 :=
      sq_le_sq' (by linarith only [hdefect, hdef_nonneg, heta_nonneg, ht_pos]) hdefect
    have hdef_mul : C * defect F (t • H) ^ 2 <= C * (eta * t) ^ 2 :=
      mul_le_mul_of_nonneg_left hdef_sq (le_of_lt hC_pos)
    have hscaled :
        t ^ 2 * highAnnulusMass J (ofPkappa kappa H) <=
          t ^ 2 * (C * eta ^ 2 + eps) := by
      calc
        t ^ 2 * highAnnulusMass J (ofPkappa kappa H)
            <= C * defect F (t • H) ^ 2 + eps * (t ^ 2 * ‖H‖ ^ 2) := hprod
        _ <= C * (eta * t) ^ 2 + eps * (t ^ 2 * ‖H‖ ^ 2) := by exact add_le_add hdef_mul (le_refl _)
        _ = t ^ 2 * (C * eta ^ 2 + eps) := by
          rw [hH_sq]
          ring
    nlinarith only [ht_sq_pos, hscaled]
end DimdPolyLEAN
