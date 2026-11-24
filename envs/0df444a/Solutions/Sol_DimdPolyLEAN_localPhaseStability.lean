-- Prove2me | solution 1 for DimdPolyLEAN.localPhaseStability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:36.971507+00:00
-- url     : https://prove2.me/submissions/4ef3bc61-e6c2-42a8-aa70-45e51595c5f2

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_norm
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_sub
public import Theorems.Thm_DimdPolyLEAN_inner_evalPkappaL2_eq_star_pkappaInner
public import Theorems.Thm_DimdPolyLEAN_realGaugeLocalStability
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_smul
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_smul
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace DimdPolyLEAN
private theorem phase_alignment
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (f0 u : H)
    (hf0 : ‖f0‖ = 1) :
    ∃ phase : ℂ, ‖phase‖ = 1 ∧
      let h := phase • (f0 + u) - f0
      (inner ℂ h f0).im = 0 ∧ ‖h‖ ≤ ‖u‖ := by
  let a : ℂ := inner ℂ f0 u
  let g : H := u - a • f0
  let β : ℂ := 1 + a
  have hf0_inner : inner ℂ f0 f0 = (1 : ℂ) := by
    simp_all
  have hg_left : inner ℂ f0 g = 0 := by
    dsimp [g, a]
    rw [inner_sub_right, inner_smul_right, hf0_inner]
    simp
  have hg_right : inner ℂ g f0 = 0 :=
    (inner_eq_zero_symm (𝕜 := ℂ) (x := g) (y := f0)).2 hg_left
  have hu_decomp : u = a • f0 + g := by
    dsimp [g]
    abel_nf
  rcases Complex.exists_norm_eq_mul_self β with ⟨phase, hphase, hphaseβ⟩
  refine ⟨phase, hphase, ?_⟩
  dsimp
  have hh_decomp :
      phase • (f0 + u) - f0 = ((phase * β - 1 : ℂ) • f0) + phase • g := by
    rw [hu_decomp, sub_eq_add_neg]
    calc
      phase • (f0 + (a • f0 + g)) + -f0
          = phase • ((1 + a) • f0 + g) + (-1 : ℂ) • f0 := by simp [add_smul, add_assoc]
      _ = (phase * β) • f0 + phase • g + (-1 : ℂ) • f0 := by simp [β, smul_add, mul_smul]
      _ = (phase * β) • f0 + (-1 : ℂ) • f0 + phase • g := by abel_nf
      _ = ((phase * β - 1 : ℂ) • f0) + phase • g := by
            rw [← add_smul]
            congr 1
  have h_inner_real :
      inner ℂ (phase • (f0 + u) - f0) f0 = ((‖β‖ - 1 : ℝ) : ℂ) := by
    rw [hh_decomp, inner_add_left, inner_smul_left, inner_smul_left, hg_right, mul_zero,
      add_zero, hf0_inner]
    have hstar : (starRingEnd ℂ) (phase * β - 1) = ((‖β‖ - 1 : ℝ) : ℂ) := by
      rw [map_sub, ← hphaseβ]
      simp
    simp [hstar]
  have himag : (inner ℂ (phase • (f0 + u) - f0) f0).im = 0 := by
    rw [h_inner_real]
    simp
  have hu_orth : inner ℂ (a • f0) g = 0 := by
    rw [inner_smul_left, hg_left]
    simp
  have hh_orth : inner ℂ (((phase * β - 1 : ℂ) • f0)) (phase • g) = 0 := by
    rw [inner_smul_left, inner_smul_right, hg_left]
    simp
  have hu_sq :
      ‖u‖ * ‖u‖ = ‖a • f0‖ * ‖a • f0‖ + ‖g‖ * ‖g‖ := by
    simpa [hu_decomp] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • f0) g hu_orth
  have hh_sq :
      ‖phase • (f0 + u) - f0‖ * ‖phase • (f0 + u) - f0‖
        = ‖((phase * β - 1 : ℂ) • f0)‖ * ‖((phase * β - 1 : ℂ) • f0)‖ +
          ‖phase • g‖ * ‖phase • g‖ := by
    rw [hh_decomp]
    simpa using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (((phase * β - 1 : ℂ) • f0)) (phase • g) hh_orth
  have hcoef : ‖(phase * β - 1 : ℂ)‖ ≤ ‖a‖ := by
    rw [← hphaseβ]
    have hreal : ((↑‖β‖ : ℂ) - 1) = (((‖β‖ - 1 : ℝ) : ℂ)) := by simp
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    simpa [β] using abs_norm_sub_norm_le β (1 : ℂ)
  have hcomp : ‖((phase * β - 1 : ℂ) • f0)‖ ≤ ‖a • f0‖ := by
    rw [norm_smul, norm_smul]
    simpa [hf0] using hcoef
  have hphase_g : ‖phase • g‖ = ‖g‖ := by rw [norm_smul, hphase, one_mul]
  have hnorm_sq_le :
      ‖phase • (f0 + u) - f0‖ * ‖phase • (f0 + u) - f0‖ ≤ ‖u‖ * ‖u‖ := by
    rw [hh_sq, hu_sq, hphase_g]
    have hcomp_sq :
        ‖((phase * β - 1 : ℂ) • f0)‖ * ‖((phase * β - 1 : ℂ) • f0)‖
          ≤ ‖a • f0‖ * ‖a • f0‖ := by
      nlinarith only [hcomp, norm_nonneg (((phase * β - 1 : ℂ) • f0)), norm_nonneg (a • f0)]
    linarith only [hcomp_sq]
  constructor
  · exact himag
  · nlinarith only [hnorm_sq_le, norm_nonneg (phase • (f0 + u) - f0), norm_nonneg u]
private theorem defect_phase_sub_eq_modulusDefect
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) {phase : ℂ} (hphase : ‖phase‖ = 1) :
    defect F (phase • Q - F) = modulusDefect kappa F Q := by
  unfold defect modulusDefect
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  have heval : evalPkappa kappa (F + (phase • Q - F)) z = phase * evalPkappa kappa Q z := by
    have h1 := congrFun (evalPkappa_smul hd kappa phase Q) z
    simp_all
  rw [heval, norm_mul, hphase, one_mul]
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
      ∀ Q : Pkappa d kappa,
        ‖Q - F‖ ≤ δ →
          ∃ phase : ℂ, ‖phase‖ = 1 ∧
            phasedCoeffDistance F Q phase ≤ Mloc * modulusDefect kappa F Q := by
  rcases realGaugeLocalStability hd kappa F hF_norm with
    ⟨δ, Mloc, hδ_pos, hMloc_pos, hreal⟩
  let S : Submodule ℂ (L2Tensor d) := polyL2Submodule hd kappa
  let f0 : S := ⟨evalPkappaL2 kappa F, ⟨F, rfl⟩⟩
  have hf0 : ‖f0‖ = 1 := by
    change ‖(f0 : L2Tensor d)‖ = 1
    simpa [f0, evalPkappaL2_norm hd kappa F] using hF_norm
  refine ⟨δ, Mloc, hδ_pos, hMloc_pos, ?_⟩
  intro Q hQδ
  let u : S := ⟨evalPkappaL2 kappa (Q - F), ⟨Q - F, rfl⟩⟩
  rcases phase_alignment f0 u hf0 with ⟨phase, hphase, hphase_gauge, hphase_norm⟩
  let H : Pkappa d kappa := phase • Q - F
  have hH_L2 :
      (phase • (f0 + u) - f0 : S) = ⟨evalPkappaL2 kappa H, ⟨H, rfl⟩⟩ := by
    apply Subtype.ext
    dsimp [H, f0, u]
    rw [evalPkappaL2_sub hd kappa (phase • Q) F, evalPkappaL2_smul hd kappa phase Q,
      evalPkappaL2_sub hd kappa Q F]
    module
  have hH_norm_le : ‖H‖ ≤ δ := by
    have hu_norm : ‖u‖ = ‖Q - F‖ := by
      change ‖(u : L2Tensor d)‖ = ‖Q - F‖
      simp [u, evalPkappaL2_norm hd kappa (Q - F)]
    have hH_norm_eq : ‖H‖ = ‖phase • (f0 + u) - f0‖ := by
      rw [hH_L2]
      change ‖H‖ = ‖evalPkappaL2 kappa H‖
      rw [evalPkappaL2_norm hd kappa H]
    calc
      ‖H‖ = ‖phase • (f0 + u) - f0‖ := hH_norm_eq
      _ ≤ ‖u‖ := hphase_norm
      _ = ‖Q - F‖ := hu_norm
      _ ≤ δ := hQδ
  have hH_gauge : (pkappaInner H F).im = 0 := by
    have hinner : (inner ℂ (evalPkappaL2 kappa H) (evalPkappaL2 kappa F)).im = 0 := by
      have hphase_gauge' :
          (inner ℂ (⟨evalPkappaL2 kappa H, ⟨H, rfl⟩⟩ : S) f0).im = 0 := by
        simpa only [← hH_L2] using hphase_gauge
      change (inner ℂ (evalPkappaL2 kappa H) (evalPkappaL2 kappa F)).im = 0 at hphase_gauge'
      exact hphase_gauge'
    have hstar_im : (star (pkappaInner H F)).im = 0 := by
      simpa [inner_evalPkappaL2_eq_star_pkappaInner hd kappa H F] using hinner
    simp_all
  refine ⟨phase, hphase, ?_⟩
  calc
    phasedCoeffDistance F Q phase = ‖H‖ := rfl
    _ ≤ Mloc * defect F H := hreal H hH_norm_le hH_gauge
    _ = Mloc * modulusDefect kappa F Q := by
          rw [defect_phase_sub_eq_modulusDefect hd kappa F Q hphase]
end DimdPolyLEAN
