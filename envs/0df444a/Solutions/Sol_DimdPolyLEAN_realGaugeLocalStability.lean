-- Prove2me | solution 1 for DimdPolyLEAN.realGaugeLocalStability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:48.379278+00:00
-- url     : https://prove2.me/submissions/2bf9cb7a-f069-4269-ba92-28a05fd94b92

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_norm
public import Theorems.Thm_DimdPolyLEAN_inner_evalPkappaL2_eq_star_pkappaInner
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_add
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_eq_toLp
public import Theorems.Thm_DimdPolyLEAN_orthogonal_coercivity
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_OrthogonalReduction_local_stability
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace DimdPolyLEAN
private theorem pkappa_ne_zero_of_norm_eq_one
    {d : Nat} {kappa : MultiIndex d} {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1) :
    F ≠ 0 := by
  intro hF_zero
  subst F
  have hzero : ‖(0 : Pkappa d kappa)‖ = 0 := by
    change
      Real.sqrt
          (Finset.sum (0 : Pkappa d kappa).support
            (fun alpha => ‖(0 : Pkappa d kappa) alpha‖ ^ 2)) = 0
    simp
  simp_all
private theorem lpNorm_congr_ae {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {f g : α → E} {p : ENNReal} {μ : Measure α} (hfg : f =ᵐ[μ] g) :
    lpNorm f p μ = lpNorm g p μ := by
  unfold lpNorm
  rw [eLpNorm_congr_ae hfg, aestronglyMeasurable_congr hfg]
private theorem gaussianL2Norm_eq_lpNorm
    {d : Nat} {α : Type*} [NormedAddCommGroup α]
     (F : Cd d → α)
    (hF : AEStronglyMeasurable F (gammaD d)) :
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      lpNorm F 2 (gammaD d) := by
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := gammaD d) (p := (2 : NNReal)) (f := F) htwo hF
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      lpNorm F (↑(2 : NNReal)) (gammaD d)
  rw [hlp]
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) ^ ((2 : ℝ)⁻¹)
  rw [Real.sqrt_eq_rpow]
  norm_num
private theorem defect_lpNorm_eq
    {d : Nat} (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    defect F G =
      lpNorm (fun z : Cd d => ‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖)
        2 (gammaD d) := by
  have hmeas :
      AEStronglyMeasurable
        (fun z : Cd d => ‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖)
        (gammaD d) :=
      (((continuous_evalPkappa kappa (F + G)).norm).sub
        ((continuous_evalPkappa kappa F).norm)).stronglyMeasurable.aestronglyMeasurable
  simpa [defect, Real.norm_eq_abs, sq_abs] using
    gaussianL2Norm_eq_lpNorm
      (fun z : Cd d => ‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖)
      hmeas
private theorem defect_lpNorm_evalPkappaL2_eq
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    defect F G =
      lpNorm
        (fun z : Cd d =>
          ‖(evalPkappaL2 kappa (G + F) : L2Tensor d) z‖ -
            ‖(evalPkappaL2 kappa F : L2Tensor d) z‖)
        2 (gammaD d) := by
  rw [defect_lpNorm_eq kappa F G]
  refine lpNorm_congr_ae ?_
  have hGF :=
    (memLp_two_evalPkappa hd kappa (G + F)).coeFn_toLp
  have hF :=
    (memLp_two_evalPkappa hd kappa F).coeFn_toLp
  filter_upwards [hGF, hF] with z hGFz hFz
  rw [evalPkappaL2_eq_toLp hd kappa (G + F),
    evalPkappaL2_eq_toLp hd kappa F]
  rw [hGFz, hFz, add_comm G F]
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ∃ δ Mloc : ℝ, 0 < δ ∧ 0 < Mloc ∧
      ∀ H : Pkappa d kappa,
        ‖H‖ ≤ δ →
          (pkappaInner H F).im = 0 →
            ‖H‖ ≤ Mloc * defect F H := by
  have hF_ne : F ≠ 0 := pkappa_ne_zero_of_norm_eq_one hF_norm
  let S : Submodule ℂ (L2Tensor d) := polyL2Submodule hd kappa
  let f0 : S := ⟨evalPkappaL2 kappa F, ⟨F, rfl⟩⟩
  have hf0 : ‖Submodule.subtypeₗᵢ S f0‖ = 1 := by
    simpa [f0, evalPkappaL2_norm hd kappa F] using hF_norm
  rcases orthogonal_coercivity (kappa := kappa) hd F hF_ne hF_norm with
    ⟨Cperp, hCperp_pos, hCperp⟩
  have hM :
      ∀ g : S, inner ℂ g f0 = 0 →
        ‖g‖ ≤ Cperp *
          lpNorm
            (fun z : Cd d =>
              ‖(Submodule.subtypeₗᵢ S (g + f0) : L2Tensor d) z‖ -
                ‖(Submodule.subtypeₗᵢ S f0 : L2Tensor d) z‖)
            2 (gammaD d) := by
    intro g hg
    rcases g.2 with ⟨G, hG⟩
    have hinner_val :
        inner ℂ (evalPkappaL2 kappa G) (evalPkappaL2 kappa F) = 0 := by
      change inner ℂ (g : L2Tensor d) (f0 : L2Tensor d) = 0 at hg
      simpa [f0, hG] using hg
    have horth : orthogonalToPk F G := by
      dsimp [orthogonalToPk]
      have hstar_zero : star (pkappaInner G F) = 0 := by
        simpa [inner_evalPkappaL2_eq_star_pkappaInner hd kappa G F] using hinner_val
      simp_all
    have hnorm_g : ‖g‖ = ‖G‖ := by
      change ‖(g : L2Tensor d)‖ = ‖G‖
      rw [← hG, evalPkappaL2_norm hd kappa G]
    have hdef := defect_lpNorm_evalPkappaL2_eq hd kappa F G
    calc
      ‖g‖ = ‖G‖ := hnorm_g
      _ ≤ Cperp * defect F G := hCperp G horth
      _ = Cperp *
          lpNorm
            (fun z : Cd d =>
              ‖(Submodule.subtypeₗᵢ S (g + f0) : L2Tensor d) z‖ -
                ‖(Submodule.subtypeₗᵢ S f0 : L2Tensor d) z‖)
            2 (gammaD d) := by
            rw [hdef]
            congr 1
            apply lpNorm_congr_ae
            filter_upwards with z
            simp [S, f0, hG, evalPkappaL2_add hd kappa G F]
  rcases OrthogonalReduction.local_stability
      (μ := gammaD d) (ι := Submodule.subtypeₗᵢ S) f0 hf0
      Cperp hCperp_pos hM with
    ⟨δ, hδ_pos, Mloc, hMloc_pos, hlocal⟩
  refine ⟨δ, Mloc, hδ_pos, hMloc_pos, ?_⟩
  intro H hHδ hH_gauge
  let h : S := ⟨evalPkappaL2 kappa H, ⟨H, rfl⟩⟩
  have hnorm_h : ‖h‖ ≤ δ := by
    have hnorm : ‖h‖ = ‖H‖ := by
      change ‖(h : L2Tensor d)‖ = ‖H‖
      simp [h, evalPkappaL2_norm hd kappa H]
    linarith only [hHδ, hnorm]
  have him_h : (inner ℂ h f0).im = 0 := by
    have hstar_im : (star (pkappaInner H F)).im = 0 := by
      simp_all
    change (inner ℂ (evalPkappaL2 kappa H) (evalPkappaL2 kappa F)).im = 0
    simpa [inner_evalPkappaL2_eq_star_pkappaInner hd kappa H F] using hstar_im
  have hlocal_h := hlocal h hnorm_h him_h
  have hnorm_h_eq : ‖h‖ = ‖H‖ := by
    change ‖(h : L2Tensor d)‖ = ‖H‖
    simp [h, evalPkappaL2_norm hd kappa H]
  have hdef := defect_lpNorm_evalPkappaL2_eq hd kappa F H
  calc
    ‖H‖ = ‖h‖ := hnorm_h_eq.symm
    _ ≤ Mloc *
        lpNorm
          (fun z : Cd d =>
            ‖(Submodule.subtypeₗᵢ S (h + f0) : L2Tensor d) z‖ -
              ‖(Submodule.subtypeₗᵢ S f0 : L2Tensor d) z‖)
          2 (gammaD d) := hlocal_h
    _ = Mloc * defect F H := by
          rw [hdef]
          congr 1
          apply lpNorm_congr_ae
          filter_upwards with z
          simp [S, f0, h, evalPkappaL2_add hd kappa H F]
end DimdPolyLEAN
