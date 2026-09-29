-- Prove2me | solution 1 for EulerMascheroni.Mixed.formal_e_system_equations
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:05:16.524437+00:00
-- url     : https://prove2.me/submissions/a581d83b-d960-464c-93f9-d215bfc765b7

import Definitions.Def_eulerMascheroni_formalESystem
set_option autoImplicit false
set_option maxHeartbeats 2000000
open PowerSeries EulerMascheroni.Mixed
namespace EulerFormalSystem
lemma ein_differential :
    X*derivative ℂ formalEin = 1-evalNegHom (exp ℂ) := by
  ext n
  cases n with
  | zero =>
    simp only [coeff_zero_X_mul, map_sub, coeff_zero_one,evalNegHom,coeff_rescale,
      coeff_exp,pow_zero,one_mul]
    norm_num
  | succ n =>
    simp only [coeff_succ_X_mul, coeff_derivative, formalEin, coeff_mk,
      einCoefficient, map_sub, coeff_one, Nat.succ_ne_zero, if_false, zero_sub,
      evalNegHom, coeff_rescale, coeff_exp]
    push_cast
    rw [pow_succ]
    field_simp
    <;> ring
lemma expEin_differential :
    X*derivative ℂ formalExpEin = X*formalExpEin+exp ℂ-1 := by
  have h1 := ein_differential
  have h2 : exp ℂ*evalNegHom (exp ℂ)=1 := exp_mul_exp_neg_eq_one
  simp only [formalExpEin, Derivation.leibniz, derivative_exp, smul_eq_mul]
  linear_combination exp ℂ*h1-h2

end EulerFormalSystem


theorem solution :
    PowerSeries.derivative ℂ (PowerSeries.exp ℂ) = PowerSeries.exp ℂ ∧
    PowerSeries.X*PowerSeries.derivative ℂ EulerMascheroni.Mixed.formalEin =
      1-PowerSeries.evalNegHom (PowerSeries.exp ℂ) ∧
    PowerSeries.X*PowerSeries.derivative ℂ EulerMascheroni.Mixed.formalExpEin =
      PowerSeries.X*EulerMascheroni.Mixed.formalExpEin+PowerSeries.exp ℂ-1 := by
  exact ⟨PowerSeries.derivative_exp ℂ, EulerFormalSystem.ein_differential, EulerFormalSystem.expEin_differential⟩

#print axioms solution
