-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.exists_f_abs_exponential_moment_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:23:39.181213+00:00
-- url     : https://prove2.me/submissions/e4d9d22e-3cb3-4234-8cf8-005f4a735fff

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_joint_integrability_factorization_readable

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
/-- **Exponential moment of `f` from the joint law.** If the joint law has an exponential moment
`e^{r‖p‖}` and `N > 0`, then `f` has the exponential moment `e^{t|f|}` with
`t = r/(2σ_β√N)` (testing the factorization at `±(r/2) e_none`). -/
theorem solution {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hexp : Integrable (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n => Real.exp (r * ‖p‖))
      (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun x => Real.exp (t * |f x|)) μ := by
  let ν := FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
  have hσ : 0 < FunctionalInequalities.KLS.LogConcave.Suspension.sigma β := by
    unfold FunctionalInequalities.KLS.LogConcave.Suspension.sigma
    apply Real.sqrt_pos.mpr
    positivity
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  let t := r / (2 * FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)
  have ht : 0 < t := div_pos hr (mul_pos (mul_pos (by norm_num) hσ) hroot)
  have hcoef : (r / 2) / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) = t := by
    dsimp [t]
    rw [div_div]
    congr 1
    ring
  let e0 : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n := EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none
  let zp : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n := (r / 2) • e0
  let zm : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n := -zp
  have hhalf : 0 < r / 2 := by positivity
  have he0norm : ‖e0‖ = 1 :=
    (EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ).norm_eq_one none
  have hzp : ‖zp‖ ≤ r := by
    dsimp [zp]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hhalf, he0norm, mul_one]
    linarith
  have hzm : ‖zm‖ ≤ r := by simpa only [zm, norm_neg] using hzp
  have hjoint (z : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n) (hz : ‖z‖ ≤ r) :
      Integrable (fun p => Real.exp ⟪z, p⟫) ν := by
    have hm : Continuous (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n => Real.exp ⟪z, p⟫) := by fun_prop
    refine hexp.mono' hm.aestronglyMeasurable ?_
    filter_upwards [] with p
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr ((real_inner_le_norm z p).trans
      (mul_le_mul_of_nonneg_right hz (norm_nonneg p)))
  let i0 : Fin N := ⟨0, hN⟩
  have hp := (FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization_readable μ hf hβ hN zp (hjoint zp hzp)).2.1 i0
  have hn := (FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization_readable μ hf hβ hN zm (hjoint zm hzm)).2.1 i0
  have hzero : (WithLp.toLp 2 (fun _ : Fin n => (0 : ℝ)) : EuclideanSpace ℝ (Fin n)) = 0 := rfl
  have hplus : Integrable (fun x => Real.exp (t * f x)) μ := by
    simpa [zp, e0, hcoef, hzero] using hp
  have hminus : Integrable (fun x => Real.exp (-t * f x)) μ := by
    simpa [zm, zp, e0, neg_div, hcoef, hzero] using hn
  refine ⟨t, ht, ?_⟩
  refine (hplus.add hminus).mono'
    ((by fun_prop : Measurable (fun x => Real.exp (t * |f x|))).aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases le_total 0 (f x) with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le
