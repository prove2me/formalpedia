-- Prove2me | solution 1 for CauchyRiemannIndex.plane_holomorphic_solutions
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T12:13:41.783102+00:00
-- url     : https://prove2.me/submissions/eeab3f5f-19b3-40d2-be20-5ec67b0dcb8c

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Measure

/-! Weighted energy identity on the plane (helpers for `plane_holomorphic_solutions`). -/

namespace PlaneHolSol

open MeasureTheory

noncomputable section

/-- Mixed partials: `∫ ∂₁A ∂_I Q = ∫ ∂_I A ∂₁Q` for `A` of class `C²` and `Q` compactly supported
`C¹`. -/
lemma integral_mixed (A Q : ℂ → ℝ) (hA : ContDiff ℝ 2 A) (hQ : ContDiff ℝ 1 Q)
    (hQc : HasCompactSupport Q) :
    ∫ z, fderiv ℝ A z 1 * fderiv ℝ Q z Complex.I =
      ∫ z, fderiv ℝ A z Complex.I * fderiv ℝ Q z 1 := by
  have hA1 : ContDiff ℝ 1 (fderiv ℝ A) := hA.fderiv_right (by norm_num)
  have hAd : ∀ v : ℂ, ContDiff ℝ 1 (fun z => fderiv ℝ A z v) := fun v =>
    hA1.clm_apply contDiff_const
  have hQd : ∀ v : ℂ, Continuous (fun z => fderiv ℝ Q z v) := fun v =>
    (hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsymm : ∀ z, fderiv ℝ (fderiv ℝ A) z Complex.I 1 = fderiv ℝ (fderiv ℝ A) z 1 Complex.I :=
    fun z => (hA.contDiffAt.isSymmSndFDerivAt (by simp)) Complex.I 1
  have hdd : ∀ v w : ℂ, ∀ z, fderiv ℝ (fun z => fderiv ℝ A z v) z w =
      fderiv ℝ (fderiv ℝ A) z w v := by
    intro v w z
    rw [fderiv_clm_apply (hA1.differentiable one_ne_zero z) (differentiableAt_const v)]
    simp
  have ibp : ∀ v w : ℂ, ∫ z, fderiv ℝ A z v * fderiv ℝ Q z w =
      -∫ z, fderiv ℝ (fderiv ℝ A) z w v * Q z := by
    intro v w
    rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
    · simp_rw [hdd]
    · simp_rw [hdd]
      exact (((hA1.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply
        continuous_const |>.mul hQ.continuous).integrable_of_hasCompactSupport hQc.mul_left
    · exact ((hAd v).continuous.mul (hQd w)).integrable_of_hasCompactSupport
        (hQc.fderiv_apply (𝕜 := ℝ) w).mul_left
    · exact ((hAd v).continuous.mul hQ.continuous).integrable_of_hasCompactSupport hQc.mul_left
    · exact fun z _ => (hAd v).differentiable one_ne_zero z
    · exact fun z _ => hQ.differentiable one_ne_zero z
  rw [ibp, ibp]
  simp_rw [hsymm]

/-- Weighted energy bound: if `∂₁A = w ∂_I B` and `∂_I A = -w ∂₁B` with `w ≥ 0`, then for every
compactly supported `C²` cut-off `χ`,
`∫ χ² w |∇B|² ≤ 4 ∫ w B² |∇χ|²`. -/
lemma energy_bound (A B w χ : ℂ → ℝ) (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B)
    (hw : Continuous w) (hw0 : ∀ z, 0 ≤ w z) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (h1 : ∀ z, fderiv ℝ A z 1 = w z * fderiv ℝ B z Complex.I)
    (h2 : ∀ z, fderiv ℝ A z Complex.I = -(w z * fderiv ℝ B z 1)) :
    ∫ z, χ z ^ 2 * w z * (fderiv ℝ B z 1 ^ 2 + fderiv ℝ B z Complex.I ^ 2) ≤
      4 * ∫ z, w z * B z ^ 2 * (fderiv ℝ χ z 1 ^ 2 + fderiv ℝ χ z Complex.I ^ 2) := by
  set Q : ℂ → ℝ := fun z => χ z * χ z * B z with hQdef
  have hB1 : ContDiff ℝ 1 B := hB.of_le (by norm_num)
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_num)
  have hQ : ContDiff ℝ 1 Q := (hχ1.mul hχ1).mul hB1
  have hQc : HasCompactSupport Q := (hχc.mul_right).mul_right
  have hdQ : ∀ z v, fderiv ℝ Q z v =
      2 * χ z * fderiv ℝ χ z v * B z + χ z ^ 2 * fderiv ℝ B z v := by
    intro z v
    have hc := (hχ1.differentiable one_ne_zero z).hasFDerivAt
    have hb := (hB1.differentiable one_ne_zero z).hasFDerivAt
    rw [HasFDerivAt.fderiv (f := Q) ((hc.mul hc).mul hb)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Pi.mul_apply]
    ring
  have hmix := integral_mixed A Q hA hQ hQc
  set dB1 : ℂ → ℝ := fun z => fderiv ℝ B z 1
  set dBI : ℂ → ℝ := fun z => fderiv ℝ B z Complex.I
  set dχ1 : ℂ → ℝ := fun z => fderiv ℝ χ z 1
  set dχI : ℂ → ℝ := fun z => fderiv ℝ χ z Complex.I
  have cB1 : Continuous dB1 := (hB1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cBI : Continuous dBI := (hB1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cχ1 : Continuous dχ1 := (hχ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cχI : Continuous dχI := (hχ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have kχ1 : HasCompactSupport dχ1 := hχc.fderiv_apply (𝕜 := ℝ) 1
  have kχI : HasCompactSupport dχI := hχc.fderiv_apply (𝕜 := ℝ) Complex.I
  set X : ℂ → ℝ := fun z => χ z ^ 2 * w z * (dB1 z ^ 2 + dBI z ^ 2)
  set Y : ℂ → ℝ := fun z => 2 * χ z * w z * B z * (dχ1 z * dB1 z + dχI z * dBI z)
  set Z : ℂ → ℝ := fun z => w z * B z ^ 2 * (dχ1 z ^ 2 + dχI z ^ 2)
  have hX : Integrable X := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact ((hχc.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)).mul_right).mul_right
  have hY : Integrable Y := by
    refine Continuous.integrable_of_hasCompactSupport
      (by have := hχ.continuous; have := hB.continuous; fun_prop) ?_
    exact (((hχc.mul_left).mul_right).mul_right).mul_right
  have hZ : Integrable Z := by
    refine Continuous.integrable_of_hasCompactSupport
      (by have := hB.continuous; fun_prop) ?_
    have : HasCompactSupport (fun z => dχ1 z ^ 2 + dχI z ^ 2) :=
      (kχ1.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)).add
        (kχI.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num))
    exact this.mul_left
  -- the identity `∫ (X + Y) = 0`
  have hXY : ∫ z, X z = -∫ z, Y z := by
    have e1 : ∀ z, fderiv ℝ A z 1 * fderiv ℝ Q z Complex.I -
        fderiv ℝ A z Complex.I * fderiv ℝ Q z 1 = X z + Y z := by
      intro z
      rw [h1, h2, hdQ, hdQ]
      simp only [X, Y, dB1, dBI, dχ1, dχI]
      ring
    have hI1 : Integrable fun z => fderiv ℝ A z 1 * fderiv ℝ Q z Complex.I := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (hQc.fderiv_apply (𝕜 := ℝ) _).mul_left
      exact ((hA.continuous_fderiv two_ne_zero).clm_apply continuous_const).mul
        ((hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    have hI2 : Integrable fun z => fderiv ℝ A z Complex.I * fderiv ℝ Q z 1 := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (hQc.fderiv_apply (𝕜 := ℝ) _).mul_left
      exact ((hA.continuous_fderiv two_ne_zero).clm_apply continuous_const).mul
        ((hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    have h0 : ∫ z, (X z + Y z) = 0 := by
      simp_rw [← e1]
      rw [integral_sub hI1 hI2, hmix, sub_self]
    rw [integral_add hX hY] at h0
    linarith
  -- pointwise `-Y ≤ X/2 + 2Z`
  have hpt : ∀ z, -Y z ≤ X z / 2 + 2 * Z z := by
    intro z
    simp only [X, Y, Z]
    have := hw0 z
    nlinarith [mul_nonneg this (sq_nonneg (χ z * dB1 z + 2 * B z * dχ1 z)),
      mul_nonneg this (sq_nonneg (χ z * dBI z + 2 * B z * dχI z))]
  have hle : ∫ z, -Y z ≤ ∫ z, (X z / 2 + 2 * Z z) :=
    integral_mono hY.neg ((hX.div_const 2).add (hZ.const_mul 2)) hpt
  rw [integral_neg, integral_add (hX.div_const 2) (hZ.const_mul 2), integral_div,
    integral_const_mul] at hle
  show ∫ z, X z ≤ 4 * ∫ z, Z z
  linarith

end

end PlaneHolSol


/-! Main argument for `plane_holomorphic_solutions`. -/

namespace PlaneHolSol

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

/-- `φ z = |z|²/2` in coordinates. -/
def phi (z : ℂ) : ℝ := (z.re ^ 2 + z.im ^ 2) / 2

lemma hasFDerivAt_phi (z : ℂ) :
    HasFDerivAt phi (z.re • Complex.reCLM + z.im • Complex.imCLM) z := by
  have h := (((Complex.reCLM.hasFDerivAt (x := z)).pow 2).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2)).mul_const (1 / 2 : ℝ)
  have e : phi = fun x => (Complex.reCLM x ^ 2 + Complex.imCLM x ^ 2) * (1 / 2 : ℝ) := by
    funext x; simp [phi]; ring
  rw [e]
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

lemma contDiff_phi : ContDiff ℝ ⊤ phi := by
  unfold phi
  have h1 : ContDiff ℝ ⊤ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have h2 : ContDiff ℝ ⊤ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  exact ((h1.pow 2).add (h2.pow 2)).div_const 2

lemma fderiv_phi (z v : ℂ) : fderiv ℝ phi z v = z.re * v.re + z.im * v.im := by
  rw [(hasFDerivAt_phi z).fderiv]
  simp

lemma phi_nonneg (z : ℂ) : 0 ≤ phi z := by unfold phi; positivity

/-- A real function on `ℂ` whose derivatives along `1` and `I` vanish has zero derivative. -/
lemma fderiv_eq_zero_of (g : ℂ → ℝ) (z : ℂ) (h1 : fderiv ℝ g z 1 = 0)
    (hI : fderiv ℝ g z Complex.I = 0) : fderiv ℝ g z = 0 := by
  ext v
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hv, map_add, map_smul, map_smul, h1, hI]
  simp

end

end PlaneHolSol


/-! Main argument for `plane_holomorphic_solutions`. -/

namespace PlaneHolSol

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

/-- Scaled cut-offs `χ_R z = χ₀ (z / R)` with `χ₀ = 1` on the unit ball, supported in the ball of
radius `2`, and `|∂_v χ_R| ≤ M / R` for unit vectors `v`. -/
lemma exists_cutoff : ∃ (χ : ℝ → ℂ → ℝ) (M : ℝ), ∀ R > 0,
    ContDiff ℝ 2 (χ R) ∧ HasCompactSupport (χ R) ∧ (∀ z, 0 ≤ χ R z ∧ χ R z ≤ 1) ∧
    (∀ z, ‖z‖ ≤ R → χ R z = 1) ∧ (∀ z, 2 * R ≤ ‖z‖ → χ R z = 0) ∧
    (∀ z v, ‖v‖ = 1 → |fderiv ℝ (χ R) z v| ≤ M * R⁻¹) := by
  let χ0 : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hχ0 : ContDiff ℝ 2 χ0 := χ0.contDiff
  obtain ⟨M, hM⟩ := (hχ0.continuous_fderiv two_ne_zero).bounded_above_of_compact_support
    (χ0.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨fun R z => χ0 (R⁻¹ • z), M, fun R hR => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (χ0.contDiff).comp (contDiff_const_smul R⁻¹)
  · exact χ0.hasCompactSupport.comp_smul (inv_ne_zero hR.ne')
  · exact fun z => ⟨χ0.nonneg, χ0.le_one⟩
  · intro z hz
    apply χ0.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hR)]
    show R⁻¹ * ‖z‖ ≤ 1
    rw [inv_mul_le_iff₀ hR]
    linarith
  · intro z hz
    apply χ0.zero_of_le_dist
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
    show 2 ≤ R⁻¹ * ‖z‖
    rw [le_inv_mul_iff₀ hR]
    linarith
  · intro z v hv
    have hd : HasFDerivAt (fun z : ℂ => χ0 (R⁻¹ • z))
        ((fderiv ℝ χ0 (R⁻¹ • z)).comp (R⁻¹ • ContinuousLinearMap.id ℝ ℂ)) z := by
      have hl : HasFDerivAt (fun z : ℂ => R⁻¹ • z) (R⁻¹ • ContinuousLinearMap.id ℝ ℂ) z :=
        ((ContinuousLinearMap.id ℝ ℂ).hasFDerivAt).const_smul R⁻¹
      exact ((hχ0.differentiable two_ne_zero) _).hasFDerivAt.comp z hl
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    calc |fderiv ℝ χ0 (R⁻¹ • z) (R⁻¹ • v)| = ‖fderiv ℝ χ0 (R⁻¹ • z) (R⁻¹ • v)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ χ0 (R⁻¹ • z)‖ * ‖R⁻¹ • v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * R⁻¹ := by
          rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
          exact mul_le_mul_of_nonneg_right (hM _) (inv_pos.2 hR).le

/-- `A = e^{φ} Re f`. -/
def fA (f : ℂ → ℂ) (z : ℂ) : ℝ := Real.exp (phi z) * (f z).re
/-- `B = e^{-φ} Im f`. -/
def fB (f : ℂ → ℂ) (z : ℂ) : ℝ := Real.exp (-phi z) * (f z).im
/-- The weight `w = e^{2φ}`. -/
def wt (z : ℂ) : ℝ := Real.exp (phi z) ^ 2

lemma hasFDerivAt_re_comp (f : ℂ → ℂ) (hf : Differentiable ℝ f) (z : ℂ) :
    HasFDerivAt (fun z => (f z).re) (Complex.reCLM.comp (fderiv ℝ f z)) z :=
  Complex.reCLM.hasFDerivAt.comp z (hf z).hasFDerivAt

lemma hasFDerivAt_im_comp (f : ℂ → ℂ) (hf : Differentiable ℝ f) (z : ℂ) :
    HasFDerivAt (fun z => (f z).im) (Complex.imCLM.comp (fderiv ℝ f z)) z :=
  Complex.imCLM.hasFDerivAt.comp z (hf z).hasFDerivAt

lemma fderiv_fA (f : ℂ → ℂ) (hf : Differentiable ℝ f) (z v : ℂ) :
    fderiv ℝ (fA f) z v = Real.exp (phi z) *
      ((z.re * v.re + z.im * v.im) * (f z).re + (fderiv ℝ f z v).re) := by
  have h := ((hasFDerivAt_phi z).exp).mul (hasFDerivAt_re_comp f hf z)
  rw [HasFDerivAt.fderiv (f := fA f) h]
  simp
  ring

lemma fderiv_fB (f : ℂ → ℂ) (hf : Differentiable ℝ f) (z v : ℂ) :
    fderiv ℝ (fB f) z v = Real.exp (-phi z) *
      (-(z.re * v.re + z.im * v.im) * (f z).im + (fderiv ℝ f z v).im) := by
  have h := ((hasFDerivAt_phi z).neg.exp).mul (hasFDerivAt_im_comp f hf z)
  rw [HasFDerivAt.fderiv (f := fB f) h]
  simp
  ring

lemma fA_fB_eqs (f : ℂ → ℂ) (hf : Differentiable ℝ f)
    (heq : ∀ z, fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I +
      z * (starRingEnd ℂ) (f z) = 0) (z : ℂ) :
    fderiv ℝ (fA f) z 1 = wt z * fderiv ℝ (fB f) z Complex.I ∧
      fderiv ℝ (fA f) z Complex.I = -(wt z * fderiv ℝ (fB f) z 1) := by
  have hr := congrArg Complex.re (heq z)
  have hi := congrArg Complex.im (heq z)
  simp at hr hi
  have he : Real.exp (phi z) * Real.exp (-phi z) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [fderiv_fA f hf, fderiv_fA f hf, fderiv_fB f hf, fderiv_fB f hf]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, wt]
  constructor
  · linear_combination (Real.exp (phi z)) * hr -
      (Real.exp (phi z) * (-(z.im * (f z).im) + (fderiv ℝ f z Complex.I).im)) * he
  · linear_combination (Real.exp (phi z)) * hi +
      (Real.exp (phi z) * (-(z.re * (f z).im) + (fderiv ℝ f z 1).im)) * he

lemma contDiff_fA (f : ℂ → ℂ) (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (fA f) :=
  (Real.contDiff_exp.comp (contDiff_phi.of_le le_top)).mul (Complex.reCLM.contDiff.comp hf)

lemma contDiff_fB (f : ℂ → ℂ) (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (fB f) :=
  (Real.contDiff_exp.comp (contDiff_phi.of_le le_top).neg).mul (Complex.imCLM.contDiff.comp hf)

lemma continuous_wt : Continuous wt := by
  unfold wt; exact (Real.continuous_exp.comp (contDiff_phi.continuous)).pow 2

lemma wt_mul_fB_sq (f : ℂ → ℂ) (z : ℂ) : wt z * fB f z ^ 2 = (f z).im ^ 2 := by
  have he : Real.exp (phi z) * Real.exp (-phi z) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold wt fB
  linear_combination ((f z).im ^ 2 * (Real.exp (phi z) * Real.exp (-phi z) + 1)) * he

/-- The derivatives of `B` vanish identically. -/
lemma fderiv_fB_eq_zero (f : ℂ → ℂ) (hf : ContDiff ℝ 2 f) (h2 : MemLp f 2 volume)
    (heq : ∀ z, fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I +
      z * (starRingEnd ℂ) (f z) = 0) (z₀ : ℂ) :
    fderiv ℝ (fB f) z₀ 1 = 0 ∧ fderiv ℝ (fB f) z₀ Complex.I = 0 := by
  obtain ⟨χ, M, hχ⟩ := exists_cutoff
  have hfd : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hA := contDiff_fA f hf
  have hB := contDiff_fB f hf
  have hB1 : ContDiff ℝ 1 (fB f) := hB.of_le (by norm_num)
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℝ, G = fun z => wt z *
      (fderiv ℝ (fB f) z 1 ^ 2 + fderiv ℝ (fB f) z Complex.I ^ 2) := ⟨_, rfl⟩
  have hGc : Continuous G := by
    rw [hGdef]
    exact continuous_wt.mul
      ((((hB1.continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2).add
        (((hB1.continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2))
  have hG0 : ∀ z, 0 ≤ G z := fun z => by
    rw [hGdef]; dsimp only; unfold wt; positivity
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℂ → ℝ, F = fun R z => χ R z ^ 2 * G z := ⟨_, rfl⟩
  have hFG : ∀ R z, F R z = χ R z ^ 2 * G z := fun R z => by rw [hFdef]
  have hFint : ∀ R > 0, Integrable (F R) := by
    intro R hR
    obtain ⟨h1, h2, -⟩ := hχ R hR
    have hc2 : HasCompactSupport (fun z => χ R z ^ 2) :=
      h2.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
    have : F R = (fun z => χ R z ^ 2) * G := funext (hFG R)
    rw [this]
    exact ((h1.continuous.pow 2).mul hGc).integrable_of_hasCompactSupport hc2.mul_right
  have hI : Integrable (fun z => ‖f z‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm h2.1).1 h2
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 8 * M ^ 2 * ∫ z, ‖f z‖ ^ 2 := ⟨_, rfl⟩
  -- the energy bound for each radius
  have hE : ∀ R > 0, ∫ z, F R z ≤ K * R⁻¹ ^ 2 := by
    intro R hR
    obtain ⟨hc, hcs, h01, -, -, hd⟩ := hχ R hR
    have eb := energy_bound (fA f) (fB f) wt (χ R) hA hB continuous_wt
      (fun z => by unfold wt; positivity) hc hcs
      (fun z => (fA_fB_eqs f hfd heq z).1) (fun z => (fA_fB_eqs f hfd heq z).2)
    have hFe : (fun z => F R z) = fun z => χ R z ^ 2 * wt z *
        (fderiv ℝ (fB f) z 1 ^ 2 + fderiv ℝ (fB f) z Complex.I ^ 2) := by
      funext z; rw [hFG, hGdef]; ring
    rw [hFe]
    refine eb.trans ?_
    have hpt : ∀ z, wt z * fB f z ^ 2 * (fderiv ℝ (χ R) z 1 ^ 2 +
        fderiv ℝ (χ R) z Complex.I ^ 2) ≤ ‖f z‖ ^ 2 * (2 * (M * R⁻¹) ^ 2) := by
      intro z
      rw [wt_mul_fB_sq]
      have h1 := hd z 1 (by simp)
      have hI' := hd z Complex.I (by simp)
      have hb : (f z).im ^ 2 ≤ ‖f z‖ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
      have q1 : fderiv ℝ (χ R) z 1 ^ 2 ≤ (M * R⁻¹) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have qI : fderiv ℝ (χ R) z Complex.I ^ 2 ≤ (M * R⁻¹) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hI' 2
      calc (f z).im ^ 2 * (fderiv ℝ (χ R) z 1 ^ 2 + fderiv ℝ (χ R) z Complex.I ^ 2)
          ≤ ‖f z‖ ^ 2 * (fderiv ℝ (χ R) z 1 ^ 2 + fderiv ℝ (χ R) z Complex.I ^ 2) :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ ≤ ‖f z‖ ^ 2 * (2 * (M * R⁻¹) ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hmono := integral_mono_of_nonneg (Eventually.of_forall fun z => by
        show (0 : ℝ) ≤ _
        unfold wt; positivity) (hI.mul_const (2 * (M * R⁻¹) ^ 2))
      (Eventually.of_forall hpt)
    rw [integral_mul_const] at hmono
    rw [hK]
    nlinarith [hmono]
  -- monotonicity in the radius
  have hmono : ∀ R₀ > 0, ∀ R ≥ 2 * R₀, ∫ z, F R₀ z ≤ ∫ z, F R z := by
    intro R₀ hR₀ R hR
    have hRpos : 0 < R := by linarith
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_) (hFint R hRpos)
      (Eventually.of_forall fun z => ?_)
    · rw [hFG]; exact mul_nonneg (sq_nonneg _) (hG0 z)
    · simp only [hFG]
      refine mul_le_mul_of_nonneg_right ?_ (hG0 z)
      obtain ⟨-, -, h01, -, hzero, -⟩ := hχ R₀ hR₀
      obtain ⟨-, -, -, hone, -, -⟩ := hχ R hRpos
      by_cases hz : ‖z‖ < 2 * R₀
      · rw [hone z (by linarith)]
        have := h01 z
        nlinarith
      · rw [hzero z (by linarith)]
        nlinarith [sq_nonneg (χ R z)]
  -- conclusion at `z₀`
  set R₀ : ℝ := ‖z₀‖ + 1
  have hR₀ : 0 < R₀ := by positivity
  have hle : ∫ z, F R₀ z ≤ 0 := by
    have ht : Tendsto (fun R : ℝ => K * R⁻¹ ^ 2) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.pow 2).const_mul K
      simpa using this
    refine ge_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop (2 * R₀)] with R hR
    exact (hmono R₀ hR₀ R hR).trans (hE R (by linarith))
  have hGz : G z₀ = 0 := by
    by_contra hne
    obtain ⟨hc, hcs, -, hone, -, -⟩ := hχ R₀ hR₀
    have hpos : 0 < ∫ z, F R₀ z := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := z₀) ?_ ?_ ?_ ?_
      · have : F R₀ = fun z => χ R₀ z ^ 2 * G z := funext (hFG R₀)
        rw [this]; exact (hc.continuous.pow 2).mul hGc
      · have : F R₀ = fun z => χ R₀ z ^ 2 * G z := funext (hFG R₀)
        rw [this]
        exact (hcs.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)).mul_right
      · intro z; show 0 ≤ F R₀ z; rw [hFG]; exact mul_nonneg (sq_nonneg _) (hG0 z)
      · rw [hFG, hone z₀ (by simp [R₀])]; simpa using hne
    linarith
  have hw : 0 < wt z₀ := by unfold wt; positivity
  have hs : fderiv ℝ (fB f) z₀ 1 ^ 2 + fderiv ℝ (fB f) z₀ Complex.I ^ 2 = 0 := by
    have : wt z₀ * (fderiv ℝ (fB f) z₀ 1 ^ 2 + fderiv ℝ (fB f) z₀ Complex.I ^ 2) = 0 := by
      rw [← hGz, hGdef]
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  constructor <;> nlinarith [sq_nonneg (fderiv ℝ (fB f) z₀ 1),
    sq_nonneg (fderiv ℝ (fB f) z₀ Complex.I)]


/-- A real function on `ℂ` with vanishing partials along `1` and `I` is constant. -/
lemma const_of_partials (g : ℂ → ℝ) (hg : Differentiable ℝ g)
    (h : ∀ z, fderiv ℝ g z 1 = 0 ∧ fderiv ℝ g z Complex.I = 0) (z : ℂ) : g z = g 0 :=
  is_const_of_fderiv_eq_zero hg (fun x => fderiv_eq_zero_of g x (h x).1 (h x).2) z 0

theorem main (f : ℂ → ℂ) (hf : ContDiff ℝ 2 f) (h2 : MemLp f 2 volume)
    (heq : ∀ z, fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I +
      z * (starRingEnd ℂ) (f z) = 0) :
    ∃ c : ℝ, ∀ z, f z = c * Complex.exp (-(‖z‖ ^ 2 / 2 : ℝ)) := by
  have hfd : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hB0 := fderiv_fB_eq_zero f hf h2 heq
  have hBc := const_of_partials (fB f) ((contDiff_fB f hf).differentiable two_ne_zero) hB0
  have he : ∀ z, Real.exp (phi z) * Real.exp (-phi z) = 1 := fun z => by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  -- `Im f = c e^{φ}` and `c = 0`
  have hb : ∀ z, (f z).im = Real.exp (phi z) * fB f 0 := by
    intro z
    rw [← hBc z]
    unfold fB
    linear_combination (-(f z).im) * he z
  have hc0 : fB f 0 = 0 := by
    by_contra hc
    have hbL : MemLp (fun z => (f z).im) 2 volume := h2.im
    have hcL : MemLp (fun _ : ℂ => |fB f 0|) 2 volume := by
      refine hbL.mono aestronglyMeasurable_const (Eventually.of_forall fun z => ?_)
      rw [hb z, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      exact le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (phi_nonneg z))
    rcases (memLp_const_iff (by norm_num) (by norm_num)).1 hcL with h | h
    · exact hc (abs_eq_zero.1 h)
    · rw [measure_univ_of_isAddLeftInvariant] at h
      exact lt_irrefl _ h
  have hA0 : ∀ z, fderiv ℝ (fA f) z 1 = 0 ∧ fderiv ℝ (fA f) z Complex.I = 0 := by
    intro z
    obtain ⟨e1, e2⟩ := fA_fB_eqs f hfd heq z
    rw [e1, e2, (hB0 z).1, (hB0 z).2]
    simp
  have hAc := const_of_partials (fA f) ((contDiff_fA f hf).differentiable two_ne_zero) hA0
  refine ⟨fA f 0, fun z => ?_⟩
  have hn : (-(‖z‖ ^ 2 / 2) : ℝ) = -phi z := by
    rw [Complex.sq_norm, Complex.normSq_apply]; unfold phi; ring
  rw [show -((‖z‖ ^ 2 / 2 : ℝ) : ℂ) = ((-phi z : ℝ) : ℂ) by rw [← hn]; push_cast; ring,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  apply Complex.ext
  · rw [Complex.ofReal_re, ← hAc z]
    unfold fA
    linear_combination (-(f z).re) * he z
  · rw [Complex.ofReal_im, hb z, hc0, mul_zero]

end

end PlaneHolSol

open scoped ContDiff in
theorem solution (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (h2 : MeasureTheory.MemLp f 2 MeasureTheory.volume)
    (heq : ∀ z, fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I +
      z * (starRingEnd ℂ) (f z) = 0) :
    ∃ c : ℝ, ∀ z, f z = c * Complex.exp (-(‖z‖ ^ 2 / 2 : ℝ)) :=
  PlaneHolSol.main f (hf.of_le (WithTop.coe_le_coe.2 le_top)) h2 heq
