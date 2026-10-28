-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:09.295421+00:00
-- url     : https://prove2.me/submissions/663cafc1-8a31-4bbe-b258-79c215c77026

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_inner_eq_fderiv_logLaplace_readable

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section LaplaceCalculus
omit [CompleteSpace E]
section NormedSpace
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma FunctionalInequalities.Analysis.BakryEmery.bkl_cumulant_swap_front [CompleteSpace F] {g : E → F} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x v w : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) g x (Fin.cons v (Fin.cons w h)) =
      iteratedFDeriv ℝ (n + 2) g x (Fin.cons w (Fin.cons v h)) := by
  have hd : ContDiff ℝ ∞ (iteratedFDeriv ℝ n g) :=
    hg.iteratedFDeriv_right (m := ∞) (by norm_cast)
  have ha : ContDiff ℝ ∞ (fun y => iteratedFDeriv ℝ n g y h) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F h).contDiff.comp hd
  have heq (a : E) :
      (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons a h)) =
        fun y => fderiv ℝ (fun z => iteratedFDeriv ℝ n g z h) y a := by
    funext y
    simpa using (hd.differentiable (by simp) y).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons a h)
  have hleft :=
    (hg.differentiable_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons v (Fin.cons w h))
  have hright :=
    (hg.differentiable_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons w (Fin.cons v h))
  rw [hleft, hright]
  simp only [Fin.tail_cons, Fin.cons_zero]
  rw [heq w, heq v]
  rw [fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiable (by norm_num) x)
      (differentiableAt_const w),
    fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiable (by norm_num) x)
      (differentiableAt_const v)]
  simpa using
    ((ha.of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)).contDiffAt.isSymmSndFDerivAt
      (by simp)).eq v w
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma FunctionalInequalities.Analysis.BakryEmery.bkl_cumulant_cons_snoc [CompleteSpace F] {g : E → F} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x v : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) g x (Fin.cons v h) =
      iteratedFDeriv ℝ (n + 1) g x (Fin.snoc h v) := by
  induction n generalizing x with
  | zero =>
      congr 1
      ext i
      fin_cases i
      simp [Fin.snoc_zero]
  | succ n ih =>
      rw [← Fin.cons_self_tail h]
      rw [bkl_cumulant_swap_front hg n x v (h 0) (Fin.tail h)]
      rw [← Fin.cons_snoc_eq_snoc_cons]
      have heq :
          (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons v (Fin.tail h))) =
            fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.snoc (Fin.tail h) v) := by
        funext y
        exact ih y (Fin.tail h)
      rw [(hg.differentiable_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left',
        (hg.differentiable_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left']
      simpa only [Fin.tail_cons, Fin.cons_zero] using
        congrArg (fun a : E → F => fderiv ℝ a x (h 0)) heq
end NormedSpace
/-- **Taylor tensors of linear functions are cumulants** (proof of BKL Proposition 7.1):
for `ℓ = ⟪v, ·⟫`, `T_d ℓ = κ_{d+1}(v, ·, …, ·) / d!`. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v : E) (d : ℕ)
    (h : Fin d → E) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => ⟪v, x⟫) d h = (d.factorial : ℝ)⁻¹ * FunctionalInequalities.Analysis.BakryEmery.cumulant μ (d + 1) (Fin.cons v h) := by
  have heq : FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ (fun x => ⟪v, x⟫) =
      fun z => fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) z v := by
    funext z
    exact FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_readable μ hexp v z
  have hL := FunctionalInequalities.Analysis.BakryEmery.contDiff_logLaplace μ hexp
  have hd : ContDiff ℝ ∞ (fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ)) :=
    hL.fderiv_right (by simp)
  have hder :
      iteratedFDeriv ℝ d (fun z => fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) z v) 0 h =
        iteratedFDeriv ℝ d (fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ)) 0 h v :=
    iteratedFDeriv_clm_apply_const_apply hd (by norm_cast; simp)
  simp only [FunctionalInequalities.Analysis.BakryEmery.taylorTensor, smul_apply, smul_eq_mul, heq]
  rw [hder]
  have hs := FunctionalInequalities.Analysis.BakryEmery.bkl_cumulant_cons_snoc hL d 0 v h
  have ht := iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ) (f := FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) (x := (0 : E)) (Fin.snoc h v)
  simp only [Fin.init_snoc, Fin.snoc_last] at ht
  rw [ht] at hs
  exact congrArg (fun a : ℝ => (d.factorial : ℝ)⁻¹ * a) hs.symm
