-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.shape_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:28:39.497065+00:00
-- url     : https://prove2.me/submissions/14dc3824-43ce-4336-9921-21f4203b8a3c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_inner_self_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_DD_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_bessel_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_jsz_line


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution (hPsi : PsiConst) (hSch : SchurH) (hBC : BeConv) (hNI : NormIdSm) (hBB : BeBessel) : Shape := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hnz
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨x0, hx0, y0, hy0, hne⟩ := hnz
  obtain ⟨ξ0, hξ0⟩ : ∃ ξ, be z c π σ μW μN x0 y0 ξ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (ContinuousLinearMap.ext hcon)
  have hB0 := hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS y0 (Or.inl hy0) ξ0
  set B0 : H → Wp := fun x => be z c π σ μW μN x y0 ξ0 with hB0def
  have hB0x : B0 x0 ≠ 0 := hξ0
  have hcoef : ∀ v ∈ DDsp σ w0, ∀ ξ : Wp, ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      be z c π σ μW μN x v ξ = κ • B0 x := fun v hv ξ =>
    jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hB0
      (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inl hv) ξ) (hsm x0 hx0) hB0x
  choose! cf hcf using hcoef
  have herm : ∀ x ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0, ∀ η ξ : Wp,
      cf v ξ * ⟪η, B0 x⟫_ℂ = conj (cf x η) * ⟪B0 v, ξ⟫_ℂ := by
    intro x hx v hv η ξ
    have hadj := (hBC4 x hx v (Or.inl hv)).2
    have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x v) ξ η
    rw [hadj, hcf v hv ξ x (hsm x hx), hcf x hx η v (hsm v hv), inner_smul_left, inner_smul_right] at e
    exact e.symm
  have hη : ⟪B0 x0, B0 x0⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hB0x
  set κ : ℂ := conj (cf x0 (B0 x0)) / ⟪B0 x0, B0 x0⟫_ℂ with hκdef
  have hcf' : ∀ v ∈ DDsp σ w0, ∀ ξ, cf v ξ = κ * ⟪B0 v, ξ⟫_ℂ := by
    intro v hv ξ
    have e := herm x0 hx0 v hv (B0 x0) ξ
    rw [hκdef, div_mul_eq_mul_div, eq_div_iff hη]
    linear_combination e
  have hform : ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ DDsp σ w0, ∀ ξ,
      be z c π σ μW μN x v ξ = (κ * ⟪B0 v, ξ⟫_ℂ) • B0 x := fun x hx v hv ξ => by
    rw [hcf v hv ξ x hx, hcf' v hv ξ]
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply hξ0
    show be z c π σ μW μN x0 y0 ξ0 = 0
    rw [hform x0 (hsm x0 hx0) y0 hy0 ξ0, h0, zero_mul, zero_smul]
  have hpos := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x0 (hsm x0 hx0) x0 (Or.inl hx0)
    (B0 x0)).2
  rw [hform x0 (hsm x0 hx0) x0 hx0, inner_smul_right, inner_self_cast] at hpos
  set N2 : ℝ := ‖B0 x0‖ ^ 2 with hN2
  have hN2pos : 0 < N2 := by rw [hN2]; have := norm_pos_iff.mpr hB0x; positivity
  have hexp : κ * (N2 : ℂ) * (N2 : ℂ) = κ * ((N2 * N2 : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hpos
  simp only [mul_zero, zero_add, sub_zero] at hpos
  have hNN : 0 < N2 * N2 := mul_pos hN2pos hN2pos
  have him : κ.im = 0 := by
    rcases mul_eq_zero.mp hpos.1 with h1 | h1
    · exact h1
    · exact absurd h1 hNN.ne'
  have hre0 : 0 ≤ κ.re := by
    by_contra hneg; push_neg at hneg
    have : κ.re * (N2 * N2) < 0 := mul_neg_of_neg_of_pos hneg hNN
    linarith [hpos.2]
  have hre : 0 < κ.re := by
    rcases hre0.lt_or_eq with h1 | h1
    · exact h1
    · exact absurd (Complex.ext (by simp [← h1]) (by simp [him])) hκ0
  set s : ℝ := Real.sqrt κ.re with hs
  have hss : (s : ℂ) * (s : ℂ) = κ := by
    rw [← Complex.ofReal_mul, hs, Real.mul_self_sqrt hre.le]
    exact Complex.ext (by simp) (by simp [him])
  have hspos : 0 < s := Real.sqrt_pos.mpr hre
  refine ⟨fun x => (s : ℂ) • B0 x, bessel_smul hB0 _, ⟨x0, hx0, ?_⟩, ?_⟩
  · exact smul_ne_zero (by exact_mod_cast hspos.ne') hB0x
  · intro x hx v hv
    ext ξ
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [hform x hx v hv ξ, inner_smul_left, Complex.conj_ofReal, smul_smul]
    congr 1
    rw [← hss]; ring
end Formalism.FourierDecayAlt.P.DDSmoothness
