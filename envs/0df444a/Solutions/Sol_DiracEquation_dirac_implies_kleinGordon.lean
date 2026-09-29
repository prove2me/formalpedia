-- Prove2me | solution 1 for DiracEquation.dirac_implies_kleinGordon
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:20:16.30748+00:00
-- url     : https://prove2.me/submissions/457809e5-28e4-49cc-b394-18120d7bca80

import Definitions.Def_DiracEquation_fields

open DiracEquation

theorem solution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g)
    (m : ℝ) (psi : (Fin 4 → ℝ) → (Fin 4 → ℂ)) (hpsi : ContDiff ℝ 2 psi)
    (hD : IsDiracSolution g m psi) : IsKleinGordonSolution m psi := by
  have hd1 : Differentiable ℝ psi := hpsi.differentiable (by norm_num)
  have hc1 : ContDiff ℝ 1 (fderiv ℝ psi) := hpsi.fderiv_right (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ psi) := hc1.differentiable (by norm_num)
  have hpd_diff : ∀ mu, Differentiable ℝ (fun y => pd psi mu y) := fun mu y => by
    unfold pd; exact (hd2 y).clm_apply (differentiableAt_const _)
  have hpd2 : ∀ mu nu x, pd2 psi mu nu x =
      fderiv ℝ (fderiv ℝ psi) x (Pi.single nu 1) (Pi.single mu 1) := by
    intro mu nu x; unfold pd2 pd
    rw [fderiv_clm_apply (hd2 x) (differentiableAt_const _)]; simp
  have hsymm : ∀ mu nu x, pd2 psi mu nu x = pd2 psi nu mu x := by
    intro mu nu x; rw [hpd2, hpd2]
    exact (hpsi.contDiffAt.isSymmSndFDerivAt (by simp)) _ _
  let M : Fin 4 → (Fin 4 → ℂ) →L[ℝ] (Fin 4 → ℂ) := fun mu =>
    LinearMap.toContinuousLinearMap ((Matrix.mulVecLin (Complex.I • g mu)).restrictScalars ℝ)
  have hM : ∀ mu v, M mu v = Complex.I • (g mu).mulVec v := by
    intro mu v; simp [M, Matrix.smul_mulVec]
  have hDfun : (fun y => ∑ mu, M mu (pd psi mu y)) = fun y => (m : ℂ) • psi y := by
    funext y; simp only [hM]; exact hD y
  have key : ∀ x nu, ∑ mu, Complex.I • (g mu).mulVec (pd2 psi mu nu x) = (m : ℂ) • pd psi nu x := by
    intro x nu
    have h1 : HasFDerivAt (fun y => ∑ mu, M mu (pd psi mu y))
        (∑ mu, (M mu).comp (fderiv ℝ (fun y => pd psi mu y) x)) x :=
      HasFDerivAt.fun_sum (fun mu _ => (M mu).hasFDerivAt.comp x (hpd_diff mu x).hasFDerivAt)
    have h2 : HasFDerivAt (fun y => (m : ℂ) • psi y) ((m : ℂ) • fderiv ℝ psi x) x :=
      (hd1 x).hasFDerivAt.const_smul (m : ℂ)
    rw [hDfun] at h1
    have h3 := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℂ) => L (Pi.single nu 1)) (h1.unique h2)
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, hM] at h3
    exact h3
  have hg' : ∀ mu nu, g mu * g nu + g nu * g mu = (2 * eta mu nu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := hg
  intro x
  set T := ∑ nu, ∑ mu, (g nu * g mu).mulVec (pd2 psi mu nu x) with hT
  have hT1 : -T = ((m : ℂ) ^ 2) • psi x := by
    have e1 : ∑ nu, Complex.I • (g nu).mulVec (∑ mu, Complex.I • (g mu).mulVec (pd2 psi mu nu x))
        = ((m : ℂ) ^ 2) • psi x := by
      simp only [key, Matrix.mulVec_smul, smul_comm Complex.I (m : ℂ)]
      rw [← Finset.smul_sum, hD x, smul_smul, pow_two]
    rw [← e1, hT, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun nu _ => ?_)
    rw [Matrix.mulVec_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun mu _ => ?_)
    rw [Matrix.mulVec_smul, smul_smul, Complex.I_mul_I, ← Matrix.mulVec_mulVec]
    simp
  have hT2 : T = ∑ nu, ∑ mu, (g mu * g nu).mulVec (pd2 psi mu nu x) := by
    rw [hT, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hsymm]
  have hT3 : T + T = (2 : ℂ) • ∑ mu, eta mu mu • pd2 psi mu mu x := by
    nth_rewrite 2 [hT2]
    rw [hT, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, ← Matrix.add_mulVec, hg']
    simp only [Fin.sum_univ_four, eta, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp
  have hT4 : T = ∑ mu, eta mu mu • pd2 psi mu mu x := by
    apply smul_right_injective _ (two_ne_zero (α := ℂ))
    simp only; rw [two_smul]; exact hT3
  rw [← hT4, ← hT1]; simp
