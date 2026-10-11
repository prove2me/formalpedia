-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.fourier_gaussD_mul_eq_zero_of_gaussExpDecay
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:19:29.860982+00:00
-- url     : https://prove2.me/submissions/dc6290b5-6097-4b43-8a76-1432381db76c

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.fourier_gaussD_mul_eq_zero_of_gaussExpDecay
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Theorems.Thm_BookProof_ScalaronHermiteEsa_norm_expGauss
import Theorems.Thm_BookProof_ScalaronHermiteEsa_GaussExpDecay_aestronglyMeasurable
import Theorems.Thm_BookProof_ScalaronHermiteEsa_integrable_pgFun_mul_of_gaussExpDecay
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ScalaronHermiteEsa




open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {u : Vd d → ℂ} (hu : GaussExpDecay u)
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ, ∫ x : Vd d, pgFun p x * u x = 0) (w : Vd d) :
    𝓕 (fun x : Vd d => ((gaussD x : ℝ) : ℂ) * u x) w = 0 := by

  set F : ℕ → Vd d → ℂ := fun N x =>
    (∑ k ∈ Finset.range N,
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
      * (((gaussD x : ℝ) : ℂ) * u x) with hF
  have hterm : ∀ p : MvPolynomial (Fin d) ℂ, Integrable (fun x : Vd d => pgFun p x * u x) :=
    fun p => integrable_pgFun_mul_of_gaussExpDecay hu p
  have hFint : ∀ N, ∫ x : Vd d, F N x = 0 := by
    intro N
    have hpt : ∀ x : Vd d, F N x = ∑ k ∈ Finset.range N,
        ((Complex.I * ((-2 * Real.pi : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
          * (pgFun ((innerPoly w) ^ k) x * u x) := by
      intro x
      simp only [hF, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pgFun_innerPoly_pow]
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun k _ => (hterm _).const_mul _)]
    simp [integral_const_mul, hmom]
  set c : ℝ := 2 * Real.pi * ‖w‖ with hc
  have hbdd : Integrable (fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) * u x) :=
    hu c
  have hgu : AEStronglyMeasurable (fun x : Vd d => ((gaussD x : ℝ) : ℂ) * u x)
      (volume : Measure (Vd d)) :=
    ((Complex.continuous_ofReal.comp continuous_gaussD).aestronglyMeasurable).mul
      hu.aestronglyMeasurable
  have hmeas : ∀ N, AEStronglyMeasurable (F N) (volume : Measure (Vd d)) := by
    intro N
    refine AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_) hgu
    refine continuous_finset_sum _ fun k _ => ?_
    refine Continuous.div_const ?_ _
    exact (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul (by fun_prop)))).pow k
  have hdom : ∀ N, ∀ᵐ x : Vd d, ‖F N x‖
      ≤ ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) * u x‖ := by
    intro N
    filter_upwards with x
    have hinner : |(inner ℝ x w : ℝ)| ≤ ‖x‖ * ‖w‖ := abs_real_inner_le_norm x w
    have hsum : ‖∑ k ∈ Finset.range N,
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
        ≤ Real.exp (c * ‖x‖) := by
      have hstep : ∀ k ∈ Finset.range N,
          ‖(Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
            ≤ (c * ‖x‖) ^ k / (k.factorial : ℝ) := by
        intro k _
        rw [norm_div, norm_pow]
        have hnum : ‖Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)‖ ≤ c * ‖x‖ := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            hc]
          have h2pi : |(-2 * Real.pi : ℝ)| = 2 * Real.pi := by
            rw [abs_of_nonpos (by nlinarith [Real.pi_pos] : (-2 * Real.pi : ℝ) ≤ 0)]; ring
          rw [h2pi]
          calc 2 * Real.pi * |(inner ℝ x w : ℝ)| ≤ 2 * Real.pi * (‖x‖ * ‖w‖) :=
                mul_le_mul_of_nonneg_left hinner (by positivity)
            _ = 2 * Real.pi * ‖w‖ * ‖x‖ := by ring
        have hden : ‖(k.factorial : ℂ)‖ = (k.factorial : ℝ) := by simp
        rw [hden]
        gcongr
      calc ‖∑ k ∈ Finset.range N,
            (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
          ≤ ∑ k ∈ Finset.range N,
              ‖(Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k
                / (k.factorial : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range N, (c * ‖x‖) ^ k / (k.factorial : ℝ) :=
            Finset.sum_le_sum hstep
        _ ≤ Real.exp (c * ‖x‖) := Real.sum_le_exp_of_nonneg (by positivity) N
    simp only [hF, norm_mul]
    have h2 : ‖((gaussD x : ℝ) : ℂ)‖ = gaussD x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussD_pos x)]
    rw [norm_expGauss, h2]
    have hg : (0 : ℝ) ≤ gaussD x * ‖u x‖ := mul_nonneg (gaussD_pos x).le (norm_nonneg _)
    calc ‖∑ k ∈ Finset.range N,
          (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
            * (gaussD x * ‖u x‖)
        ≤ Real.exp (c * ‖x‖) * (gaussD x * ‖u x‖) := mul_le_mul_of_nonneg_right hsum hg
      _ = Real.exp (c * ‖x‖) * gaussD x * ‖u x‖ := by ring
  have hlim : ∀ᵐ x : Vd d, Filter.Tendsto (fun N => F N x) Filter.atTop
      (nhds (Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
        * (((gaussD x : ℝ) : ℂ) * u x))) := by
    filter_upwards with x
    have hsum := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ)
      (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)))
    have hsum' : HasSum (fun k : ℕ =>
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
        (Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))) := by
      simpa [Complex.exp_eq_exp_ℂ] using hsum
    exact hsum'.tendsto_sum_nat.mul_const _
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : Vd d => ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) * u x‖)
    hmeas hbdd.norm hdom hlim
  have hval : ∫ x : Vd d, Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
      * (((gaussD x : ℝ) : ℂ) * u x) = 0 := by
    have hc0 : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop
        (nhds (∫ x : Vd d, Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
          * (((gaussD x : ℝ) : ℂ) * u x))) := by
      simpa [hFint] using hconv
    exact tendsto_nhds_unique hc0 tendsto_const_nhds
  rw [Real.fourier_eq', ← hval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring
