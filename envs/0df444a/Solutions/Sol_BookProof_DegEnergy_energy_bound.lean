-- Prove2me | solution 1 for BookProof.DegEnergy.energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T16:12:47.818146+00:00
-- url     : https://prove2.me/submissions/b70fdbf1-e253-470b-8165-c98b16230e34

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.energy_bound
import Mathlib
import Definitions.Def_ChapterDegEnergyEstimate
import Theorems.Thm_BookProof_DegEnergy_dcoord_conj
import Theorems.Thm_BookProof_DegEnergy_integrable_of_cc
import Theorems.Thm_BookProof_DegEnergy_integral_dcoord_mul
import Theorems.Thm_BookProof_DegEnergy_contDiff_cx
import Theorems.Thm_BookProof_DegEnergy_hasCompactSupport_cx
import Theorems.Thm_BookProof_DegEnergy_norm_cx
import Theorems.Thm_BookProof_DegEnergy_integral_cx_sq_mul_normSq
import Theorems.Thm_BookProof_DegEnergy_dcoord_cx_sq
import Theorems.Thm_BookProof_ConvolutionCalc_hasCompactSupport_dcoord
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterHermiteProductCore
open BookProof.DegEnergy




open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger
open BookProof.ConvolutionCalc
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable (S : Finset (Fin d))

set_option maxHeartbeats 1000000 in
theorem solution {z : ℂ} (hz : z.re = 0) {v G : Vd d → ℂ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (hG : Continuous G)
    (hid : ∀ x, lapCS S v x = G x - z * v x)
    {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ) :
    (∫ x, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * G x).re
      ≤ 2 * ∑ j ∈ S, ∫ x, ‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2 := by

  classical
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cx χ) := contDiff_cx hχ
  have hcc : HasCompactSupport (cx χ) := hasCompactSupport_cx hχc
  have hcxc : Continuous (cx χ) := hcs.continuous
  have hvc : Continuous v := hv.continuous
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (starRingEnd ℂ) (v y)) :=
    Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.contDiff.comp hv
  have hconjc : Continuous (fun y : Vd d => (starRingEnd ℂ) (v y)) := hconj.continuous
  have hcc2 : HasCompactSupport (fun x : Vd d => cx χ x ^ 2) := by
    refine hcc.mono ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h0
    exact hx (by rw [h0]; ring)
  set f : Vd d → ℂ := fun x => cx χ x ^ 2 * (starRingEnd ℂ) (v x) with hf
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := (hcs.pow 2).mul hconj
  have hfc : HasCompactSupport f := hcc2.mul_right
  have hdvs : ∀ j : Fin d, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dcoord j v) :=
    fun j => contDiff_dcoord hv j
  have hdvc : ∀ j : Fin d, Continuous (dcoord j v) := fun j => (hdvs j).continuous
  have hdcs : ∀ j : Fin d, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dcoord j (cx χ)) :=
    fun j => contDiff_dcoord hcs j
  have hdcxc : ∀ j : Fin d, Continuous (dcoord j (cx χ)) := fun j => (hdcs j).continuous
  have hdcc : ∀ j : Fin d, HasCompactSupport (dcoord j (cx χ)) :=
    fun j => hasCompactSupport_dcoord hcc j
  -- the derivative of the test factor
  have hdf : ∀ (j : Fin d) (x : Vd d), dcoord j f x
      = 2 * cx χ x * dcoord j (cx χ) x * (starRingEnd ℂ) (v x)
        + cx χ x ^ 2 * (starRingEnd ℂ) (dcoord j v x) := by
    intro j x
    have h1 := congrFun (dcoord_mul (u := fun y => cx χ y ^ 2)
        (v := fun y => (starRingEnd ℂ) (v y)) (hcs.pow 2) hconj j) x
    rw [hf, h1, dcoord_cx_sq hχ j x, dcoord_conj hv j x]
    ring
  -- the two pieces of the boundary term
  set X : Fin d → ℂ := fun j => ∫ x, 2 * cx χ x * dcoord j (cx χ) x * (starRingEnd ℂ) (v x)
    * dcoord j v x with hX
  set Y : Fin d → ℂ := fun j => ∫ x, cx χ x ^ 2 * (starRingEnd ℂ) (dcoord j v x)
    * dcoord j v x with hY
  set Yr : Fin d → ℝ := fun j => ∫ x, (χ x) ^ 2 * ‖dcoord j v x‖ ^ 2 with hYr
  set Qr : Fin d → ℝ := fun j => ∫ x, ‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2 with hQr
  -- integrability of all the integrands in play
  have hIX : ∀ j : Fin d, Integrable (fun x => 2 * cx χ x * dcoord j (cx χ) x
      * (starRingEnd ℂ) (v x) * dcoord j v x) (volume : Measure (Vd d)) := fun j =>
    integrable_of_cc
      ((((continuous_const.mul hcxc).mul (hdcxc j)).mul hconjc).mul (hdvc j))
      (((hdcc j).mul_left).mul_right.mul_right)
  have hIY : ∀ j : Fin d, Integrable (fun x => cx χ x ^ 2 * (starRingEnd ℂ) (dcoord j v x)
      * dcoord j v x) (volume : Measure (Vd d)) := fun j =>
    integrable_of_cc
      (((hcxc.pow 2).mul ((Complex.continuous_conj).comp (hdvc j))).mul (hdvc j))
      (hcc2.mul_right.mul_right)
  have hIfd : ∀ j : Fin d, Integrable (fun x => f x * dcoord j (dcoord j v) x)
      (volume : Measure (Vd d)) := fun j =>
    integrable_of_cc (hfs.continuous.mul (contDiff_dcoord (hdvs j) j).continuous) hfc.mul_right
  have hIfG : Integrable (fun x => f x * G x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hfs.continuous.mul hG) hfc.mul_right
  have hIfv : Integrable (fun x => f x * v x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hfs.continuous.mul hvc) hfc.mul_right
  -- integration by parts in each direction of `S`
  have hIBPj : ∀ j : Fin d, ∫ x, f x * dcoord j (dcoord j v) x = -(X j + Y j) := by
    intro j
    rw [integral_dcoord_mul hfs hfc (hdvs j) j, hX, hY, ← integral_add (hIX j) (hIY j)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change dcoord j f x * dcoord j v x = _
    rw [hdf j x]
    ring
  -- the energy identity
  have hEnergy : ∫ x, f x * G x = z * (∫ x, f x * v x) + ∑ j ∈ S, -(X j + Y j) := by
    have hsplit : ∫ x, f x * lapCS S v x = ∑ j ∈ S, ∫ x, f x * dcoord j (dcoord j v) x := by
      rw [← MeasureTheory.integral_finset_sum S (fun j _ => hIfd j)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [lapCS, Finset.mul_sum]
    have hlhs : ∫ x, f x * lapCS S v x = (∫ x, f x * G x) - z * ∫ x, f x * v x := by
      have hpt : ∀ x, f x * lapCS S v x = f x * G x - z * (f x * v x) := by
        intro x
        rw [hid x]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_sub hIfG ((hIfv.const_mul z)), integral_const_mul]
    rw [hlhs] at hsplit
    rw [Finset.sum_congr rfl (fun j _ => (hIBPj j).symm), ← hsplit]
    ring
  -- the mass term is real
  have hreal : ∫ x, f x * v x = (((∫ x, (χ x) ^ 2 * ‖v x‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hf]
    exact integral_cx_sq_mul_normSq v x
  -- the gradient terms are real and non-negative
  have hYreal : ∀ j : Fin d, Y j = ((Yr j : ℝ) : ℂ) := by
    intro j
    rw [hY, hYr]
    simp only
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact integral_cx_sq_mul_normSq (dcoord j v) x
  have hYrnonneg : ∀ j : Fin d, 0 ≤ Yr j := by
    intro j
    rw [hYr]
    exact integral_nonneg fun x => by positivity
  -- Young's inequality absorbs the boundary term
  have hchi2c : HasCompactSupport (fun x : Vd d => (χ x) ^ 2) := by
    refine hχc.mono ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h0
    exact hx (by rw [h0]; ring)
  have hdc2 : ∀ j : Fin d, HasCompactSupport (fun x : Vd d => ‖dcoord j (cx χ) x‖ ^ 2) := by
    intro j
    refine (hdcc j).mono ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h0
    exact hx (by rw [h0]; simp)
  have hIYr : ∀ j : Fin d, Integrable (fun x => (χ x) ^ 2 * ‖dcoord j v x‖ ^ 2)
      (volume : Measure (Vd d)) := fun j =>
    ((hχ.continuous.pow 2).mul ((hdvc j).norm.pow 2)).integrable_of_hasCompactSupport
      hchi2c.mul_right
  have hIQr : ∀ j : Fin d, Integrable (fun x => ‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2)
      (volume : Measure (Vd d)) := fun j =>
    (((hdcxc j).norm.pow 2).mul (hvc.norm.pow 2)).integrable_of_hasCompactSupport
      (hdc2 j).mul_right
  have hXbound : ∀ j : Fin d, -(X j).re ≤ Yr j / 2 + 2 * Qr j := by
    intro j
    have h1 : -(X j).re ≤ ‖X j‖ := by
      have habs := Complex.abs_re_le_norm (X j)
      have := abs_le.mp habs
      linarith [this.1]
    have h2 : ‖X j‖ ≤ ∫ x, ‖2 * cx χ x * dcoord j (cx χ) x * (starRingEnd ℂ) (v x)
        * dcoord j v x‖ := by
      rw [hX]
      exact norm_integral_le_integral_norm _
    have h3 : ∫ x, ‖2 * cx χ x * dcoord j (cx χ) x * (starRingEnd ℂ) (v x) * dcoord j v x‖
        ≤ ∫ x, ((χ x) ^ 2 * ‖dcoord j v x‖ ^ 2 / 2
            + 2 * (‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2)) := by
      refine integral_mono ((hIX j).norm) (((hIYr j).div_const 2).add ((hIQr j).const_mul 2))
        fun x => ?_
      have hnorm : ‖2 * cx χ x * dcoord j (cx χ) x * (starRingEnd ℂ) (v x) * dcoord j v x‖
          = 2 * (|χ x| * ‖dcoord j v x‖) * (‖dcoord j (cx χ) x‖ * ‖v x‖) := by
        simp only [norm_mul, norm_cx, RCLike.norm_conj]
        norm_num
        ring
      have hsq : (χ x) ^ 2 = |χ x| ^ 2 := (sq_abs _).symm
      simp only [hnorm, hsq]
      nlinarith [sq_nonneg (|χ x| * ‖dcoord j v x‖ - 2 * (‖dcoord j (cx χ) x‖ * ‖v x‖)),
        abs_nonneg (χ x), norm_nonneg (dcoord j v x), norm_nonneg (dcoord j (cx χ) x),
        norm_nonneg (v x)]
    have h4 : ∫ x, ((χ x) ^ 2 * ‖dcoord j v x‖ ^ 2 / 2
        + 2 * (‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2)) = Yr j / 2 + 2 * Qr j := by
      rw [integral_add ((hIYr j).div_const 2) ((hIQr j).const_mul 2), integral_div,
        integral_const_mul]
    linarith
  -- conclusion
  have hgoal : (∫ x, f x * G x).re = -∑ j ∈ S, ((X j).re + Yr j) := by
    rw [hEnergy]
    simp only [Complex.add_re, Complex.mul_re, hreal, Complex.ofReal_re, Complex.ofReal_im, hz]
    have : (∑ j ∈ S, -(X j + Y j)).re = ∑ j ∈ S, -((X j).re + Yr j) := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hYreal j]
      simp
    rw [this, Finset.sum_neg_distrib]
    ring
  have hfinal : -∑ j ∈ S, ((X j).re + Yr j) ≤ 2 * ∑ j ∈ S, Qr j := by
    have hterm : ∀ j ∈ S, -((X j).re + Yr j) ≤ 2 * Qr j := by
      intro j _
      have := hXbound j
      have := hYrnonneg j
      linarith
    calc -∑ j ∈ S, ((X j).re + Yr j) = ∑ j ∈ S, -((X j).re + Yr j) := by
          rw [Finset.sum_neg_distrib]
      _ ≤ ∑ j ∈ S, 2 * Qr j := Finset.sum_le_sum hterm
      _ = 2 * ∑ j ∈ S, Qr j := by rw [Finset.mul_sum]
  calc (∫ x, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * G x).re = (∫ x, f x * G x).re := by
        rw [hf]
    _ = -∑ j ∈ S, ((X j).re + Yr j) := hgoal
    _ ≤ 2 * ∑ j ∈ S, Qr j := hfinal
