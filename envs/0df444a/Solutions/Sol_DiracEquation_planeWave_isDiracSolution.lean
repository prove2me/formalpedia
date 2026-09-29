-- Prove2me | solution 1 for DiracEquation.planeWave_isDiracSolution
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:20:04.608555+00:00
-- url     : https://prove2.me/submissions/9cac9997-4c10-49b3-bb84-a3ac62c7c14a

import Definitions.Def_DiracEquation_fields

open DiracEquation

namespace Ag1Aux_DiracPlane

theorem mulVec_slash (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (p : Fin 4 → ℂ) (u : Fin 4 → ℂ) :
    (slash g p).mulVec u = ∑ mu, p mu • (g mu).mulVec u := by
  simp [slash, Matrix.sum_mulVec, Matrix.smul_mulVec]

theorem pd_planeWave (p : Fin 4 → ℝ) (u : Fin 4 → ℂ) (mu : Fin 4) (x : Fin 4 → ℝ) :
    pd (planeWave p u) mu x =
      (Complex.exp (Complex.I * ∑ nu, (p nu : ℂ) * (x nu : ℂ)) * (Complex.I * p mu)) • u := by
  let L : (Fin 4 → ℝ) →L[ℝ] ℂ :=
    ∑ nu, (Complex.I * (p nu : ℂ)) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj nu))
  have hL : ∀ y : Fin 4 → ℝ, L y = Complex.I * ∑ nu, (p nu : ℂ) * (y nu : ℂ) := by
    intro y
    simp [L, Finset.mul_sum, mul_assoc]
  have hfun : planeWave p u = fun y => Complex.exp (L y) • u := by
    funext y; simp [planeWave, hL]
  have hd : HasFDerivAt (fun y => Complex.exp (L y) • u)
      ((Complex.exp (L x) • L).smulRight u) x := (L.hasFDerivAt.cexp).smul_const u
  unfold pd
  rw [hfun, hd.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply]
  rw [hL x]
  congr 1
  simp [L, Pi.single_apply]
  rw [Finset.sum_eq_single mu (fun b _ hb => by simp [hb]) (by simp)]
  simp

end Ag1Aux_DiracPlane

open Ag1Aux_DiracPlane

theorem solution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (m : ℝ) (p : Fin 4 → ℝ)
    (u : Fin 4 → ℂ)
    (hu : (slash g fun mu => (p mu : ℂ)).mulVec u + (m : ℂ) • u = 0) :
    IsDiracSolution g m (planeWave p u) := by
  intro x
  have h1 : ∑ mu, (p mu : ℂ) • (g mu).mulVec u = -((m : ℂ) • u) := by
    rw [← mulVec_slash g (fun mu => (p mu : ℂ)) u]; exact eq_neg_of_add_eq_zero_left hu
  simp only [pd_planeWave]
  set E := Complex.exp (Complex.I * ∑ nu, (p nu : ℂ) * (x nu : ℂ))
  have : ∀ mu, Complex.I • (g mu).mulVec ((E * (Complex.I * p mu)) • u)
      = (-E) • ((p mu : ℂ) • (g mu).mulVec u) := by
    intro mu
    rw [Matrix.mulVec_smul, smul_smul, smul_smul]
    congr 1
    ring_nf; rw [Complex.I_sq]; ring
  rw [Finset.sum_congr rfl (fun mu _ => this mu), ← Finset.smul_sum, h1]
  show (-E) • -((m : ℂ) • u) = (m : ℂ) • (E • u)
  rw [neg_smul, smul_neg, neg_neg, smul_smul, smul_smul, mul_comm]
