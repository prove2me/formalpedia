-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.tendsto_slope_phaseUnitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T20:29:35.653991+00:00
-- url     : https://prove2.me/submissions/2f4c6b9a-df6d-4573-8c63-3605db7c62be

-- Generated from ChapterUnboundedPosition.lean — solution of BookProof.ChapterUnboundedPosition.tendsto_slope_phaseUnitary
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNsLagrangianDetConvolution
import Definitions.Def_ChapterLeafGaps
open BookProof.ChapterUnboundedPosition



open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

set_option maxHeartbeats 1000000 in
theorem solution (f : ℤ → ℝ) (psi : mulDomain f) :
    Filter.Tendsto (fun t : ℝ => (t⁻¹ : ℝ) • (phaseUnitary f t (psi : L2Z) - (psi : L2Z)))
      (nhdsWithin 0 {0}ᶜ) (nhds (Complex.I • mulOp f psi)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    set g : ℤ → ℂ := fun k => (psi : L2Z) k with hg
    have hsq : ∀ t : ℝ,
        ‖(t⁻¹ : ℝ) • (phaseUnitary f t (psi : L2Z) - (psi : L2Z)) - Complex.I • mulOp f psi‖ ^ 2
          = ∑' k : ℤ, ‖((t⁻¹ : ℝ) • (phase f t k - 1)) * g k - Complex.I * (f k : ℂ) * g k‖ ^ 2 := by
      intro t
      rw [BookProof.ChapterContinuityUnitaryInfinite.norm_sq_eq_tsum]
      refine tsum_congr fun k => ?_
      congr 1
      simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        phaseUnitary_apply, phaseLin_apply, mulOp_apply, Complex.real_smul, hg]
      ring
    have hfpsi : Summable fun k : ℤ => ‖(f k : ℂ) * g k‖ ^ 2 := by
      simpa [hg] using
        BookProof.ChapterContinuityUnitaryInfinite.summable_normSq (mulOp f psi)
    have hbound : Summable fun k : ℤ => 4 * ‖(f k : ℂ) * g k‖ ^ 2 := hfpsi.mul_left 4
    have hpt : ∀ k : ℤ, Filter.Tendsto
        (fun t : ℝ => ‖((t⁻¹ : ℝ) • (phase f t k - 1)) * g k - Complex.I * (f k : ℂ) * g k‖ ^ 2)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      intro k
      have h1 := (tendsto_slope_phase f k).mul_const (g k)
      have h2 : Filter.Tendsto
          (fun t : ℝ => ((t⁻¹ : ℝ) • (phase f t k - 1)) * g k - Complex.I * (f k : ℂ) * g k)
          (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
        have := h1.sub_const (Complex.I * (f k : ℂ) * g k)
        simpa [mul_assoc] using this
      simpa using (h2.norm.pow 2)
    have hdom : ∀ t : ℝ, ∀ k : ℤ,
        ‖‖((t⁻¹ : ℝ) • (phase f t k - 1)) * g k - Complex.I * (f k : ℂ) * g k‖ ^ 2‖
          ≤ 4 * ‖(f k : ℂ) * g k‖ ^ 2 := by
      intro t k
      have hph : ‖((t⁻¹ : ℝ) • (phase f t k - 1))‖ ≤ |f k| := by
        rcases eq_or_ne t 0 with rfl | ht
        · simp
        · have hbase : ‖phase f t k - 1‖ ≤ |t * f k| := by
            simpa [phase, Real.norm_eq_abs] using
              (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * f k))
          rw [norm_smul, Real.norm_eq_abs, abs_inv]
          calc |t|⁻¹ * ‖phase f t k - 1‖ ≤ |t|⁻¹ * |t * f k| :=
                mul_le_mul_of_nonneg_left hbase (by positivity)
            _ = |f k| := by
                rw [abs_mul, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.2 ht), one_mul]
      have h1 : ‖((t⁻¹ : ℝ) • (phase f t k - 1)) * g k - Complex.I * (f k : ℂ) * g k‖
          ≤ 2 * ‖(f k : ℂ) * g k‖ := by
        have e1 : ‖((t⁻¹ : ℝ) • (phase f t k - 1)) * g k‖ ≤ |f k| * ‖g k‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hph (norm_nonneg _)
        have e2 : ‖Complex.I * (f k : ℂ) * g k‖ = |f k| * ‖g k‖ := by
          simp [Complex.norm_real, Real.norm_eq_abs, mul_assoc]
        have e3 : ‖(f k : ℂ) * g k‖ = |f k| * ‖g k‖ := by
          simp [Complex.norm_real, Real.norm_eq_abs]
        calc ‖((t⁻¹ : ℝ) • (phase f t k - 1)) * g k - Complex.I * (f k : ℂ) * g k‖
            ≤ ‖((t⁻¹ : ℝ) • (phase f t k - 1)) * g k‖ + ‖Complex.I * (f k : ℂ) * g k‖ :=
              norm_sub_le _ _
          _ ≤ |f k| * ‖g k‖ + |f k| * ‖g k‖ := by rw [e2]; linarith
          _ = 2 * ‖(f k : ℂ) * g k‖ := by rw [e3]; ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (((t⁻¹ : ℝ) • (phase f t k - 1)) * g k -
        Complex.I * (f k : ℂ) * g k), norm_nonneg ((f k : ℂ) * g k)]
    have htsum := tendsto_tsum_of_dominated_convergence hbound hpt
      (Filter.Eventually.of_forall hdom)
    rw [tsum_zero] at htsum
    have hsqrt : Filter.Tendsto
        (fun t : ℝ => Real.sqrt (∑' k : ℤ,
          ‖((t⁻¹ : ℝ) • (phase f t k - 1)) * g k - Complex.I * (f k : ℂ) * g k‖ ^ 2))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      simpa using! (Real.continuous_sqrt.tendsto 0).comp htsum
    refine hsqrt.congr fun t => ?_
    rw [← hsq t, Real.sqrt_sq (norm_nonneg _)]
