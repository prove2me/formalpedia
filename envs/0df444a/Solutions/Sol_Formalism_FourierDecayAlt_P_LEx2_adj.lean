-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:44.231948+00:00
-- url     : https://prove2.me/submissions/adc1ca81-2512-4ee8-bb1e-585256cad662

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_L3
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A3_dS_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A3_dsMeas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_dS_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_pr
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_pr_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_smoothLog_sc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_ld_zero__1805213b0513
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_sq_nonneg__b7974ad0744f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : Adj := by
  intro hC hLeib hCT hCI hTS hTR B S c σ h4 hM hW hI3 hAdj hJet hI4 hI4' hInt ε hε Y hY
  have hσ : 0 ≤ σ := by linarith
  have hd : ∀ ω k, 0 ≤ S.d Y ω k := fun ω k => (hW.2 Y hY ω k).le
  have hdw : ∀ ω i, 0 ≤ S.dw ω i := fun ω i => (hW.1 ω i).le
  have hth : ∀ ω, 0 ≤ th ε σ (B.G ω) ∧ th ε σ (B.G ω) ≤ 1 := fun ω =>
    ⟨(hTR ε σ (B.G ω) hε hσ (B.G_pos ω)).1.le, (hTR ε σ (B.G ω) hε hσ (B.G_pos ω)).2⟩
  have hds0 : S.ds Y 0 = S.gX Y := dS_zero B _ _
  have hmds : ∀ p k, Measurable fun ω => S.ds Y p ω k := fun p k => A3.dsMeas B S hM hI4 Y hY p k
  have hmg : ∀ k, Measurable fun ω => S.gX Y ω k := by
    intro k
    have := hmds 0 k
    rwa [hds0] at this
  have hci := hCI B S σ hσ hM hW hI4 hI4' ε hε Y hY
  have hsm : ∀ ε₂ : ℝ, SmoothLog (fun y => c.sc ε₂ 1 y * th ε σ y) := fun ε₂ =>
    ContDiff.mul (smoothLog_sc c ε₂ 1) (hTS ε σ hε)

  set hL : B.Ω → ℂ := fun ω => ((|S.P Y| * LE.sq B S.dw S.X ω : ℝ) : ℂ) with hLdef
  have hsq0 : ∀ ω, 0 ≤ LE.sq B S.dw S.X ω := sq_nonneg' B _ hdw _
  have l0 := L3 hC hCT hTS hTR B c σ ε h4 hε 0 hL
    (Complex.measurable_ofReal.comp_aemeasurable (hInt.1.aemeasurable.const_mul _)).aestronglyMeasurable
    (fun ω => |S.P Y| * LE.sq B S.dw S.X ω) (hInt.const_mul _) (by
      intro ω
      rw [hLdef]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (hsq0 ω))]
      exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (hsq0 ω)) (hth ω).2)

  have lp := fun p => L3 hC hCT hTS hTR B c σ ε h4 hε p (pr B (S.d Y) (S.gX Y) (S.ds Y p))
    (meas_pr B (S.d Y) _ _ ((hM.2.2 Y hY).1) hmg (hmds p)).aestronglyMeasurable
    (fun ω => (th ε σ (B.G ω) * LE.sq B (S.d Y) (S.ds Y 0) ω / 1 + 1 * (th ε σ (B.G ω) * LE.sq B (S.d Y) (S.ds Y p) ω)) / 2)
    ((((hci 0).div_const 1).add ((hci p).const_mul 1)).div_const 2) (by
      intro ω
      have := mul_le_mul_of_nonneg_left (pr_bound B (S.d Y) hd (S.gX Y) (S.ds Y p) 1 one_pos ω) (hth ω).1
      rw [hds0]
      calc _ ≤ _ := this
        _ = _ := by ring)
  have hleft : ∀ ε₂ : ℝ, ∀ ω, pr B (fun _ _ => 1) (S.gst Y (fun ω k => (S.d Y ω k : ℂ) * S.gX Y ω k))
      (mulF B (fun y => c.sc ε₂ 1 y * th ε σ y) S.X) ω =
      (ld 0 (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * hL ω := by
    intro ε₂ ω
    rw [ld_zero' _ _ (B.G_pos ω), hLdef]
    unfold pr LE.sq mulF
    simp_rw [hI3 Y hY ω]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have e := Complex.mul_conj' (S.X ω i)
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination ((c.sc ε₂ 1 (B.G ω) : ℂ) * (th ε σ (B.G ω) : ℂ) * ((|S.P Y| : ℝ) : ℂ) * (S.dw ω i : ℂ)) * e
  have hright : ∀ ε₂ : ℝ, ∀ ω, pr B (S.d Y) (S.gX Y) (S.g Y (mulF B (fun y => c.sc ε₂ 1 y * th ε σ y) S.X)) ω =
      ∑ p ∈ range (S.r + 2), (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) *
        pr B (S.d Y) (S.gX Y) (S.ds Y p) ω / p.factorial := by
    intro ε₂ ω
    unfold pr
    simp_rw [hLeib B _ _ (S.g Y) S.X (S.r + 1) (hJet Y hY) (hI4 Y hY) _ (hsm ε₂) ω]
    simp only [map_sum, map_div₀, map_mul, Complex.conj_ofReal, map_natCast, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro k _
    show _ = _ * (_ * _ * conj (dS B (S.g Y) S.X p ω k)) / _
    ring
  have heq : (fun ε₂ : ℝ => ∫ ω, (ld 0 (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * hL ω ∂B.μ) =ᶠ[𝓝[>] 0]
      fun ε₂ : ℝ => ∑ p ∈ range (S.r + 2), (∫ ω, (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) *
        pr B (S.d Y) (S.gX Y) (S.ds Y p) ω ∂B.μ) / p.factorial := by
    filter_upwards [self_mem_nhdsWithin] with ε₂ h2
    have h := hAdj Y hY ε ε₂ hε h2
    simp_rw [hleft ε₂, hright ε₂] at h
    rw [h, integral_finset_sum _ (fun p _ => ((lp p).1 ε₂ h2).div_const _)]
    apply Finset.sum_congr rfl
    intro p _
    rw [integral_div]
  have lsum : Tendsto (fun ε₂ : ℝ => ∑ p ∈ range (S.r + 2),
      (∫ ω, (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) *
        pr B (S.d Y) (S.gX Y) (S.ds Y p) ω ∂B.μ) / p.factorial) (𝓝[>] 0)
      (𝓝 (∑ p ∈ range (S.r + 2), S.term ε σ Y p)) := by
    apply tendsto_finset_sum
    intro p _
    exact ((lp p).2).div_const _
  have hfin := tendsto_nhds_unique (l0.2.congr' heq) lsum
  rw [← hfin]
  have e3 : (fun ω => (ld 0 (th ε σ) (B.G ω) : ℂ) * hL ω) =
      fun ω => ((|S.P Y| * (th ε σ (B.G ω) * LE.sq B S.dw S.X ω) : ℝ) : ℂ) := by
    funext ω
    rw [ld_zero' _ _ (B.G_pos ω), hLdef]; push_cast; ring
  rw [e3]
  have e4 : ∫ ω, ((|S.P Y| * (th ε σ (B.G ω) * LE.sq B S.dw S.X ω) : ℝ) : ℂ) ∂B.μ =
      ((∫ ω, |S.P Y| * (th ε σ (B.G ω) * LE.sq B S.dw S.X ω) ∂B.μ : ℝ) : ℂ) := integral_ofReal
  rw [e4, integral_const_mul]
  rfl
end Formalism.FourierDecayAlt.P.LEx2
