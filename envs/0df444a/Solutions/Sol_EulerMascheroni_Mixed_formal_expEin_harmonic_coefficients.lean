-- Prove2me | solution 1 for EulerMascheroni.Mixed.formal_expEin_harmonic_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:15:23.668786+00:00
-- url     : https://prove2.me/submissions/c36543fa-5388-4031-85f7-856ab13255ff

import Theorems.Thm_EulerMascheroni_Mixed_formal_e_system_equations
set_option autoImplicit false
open PowerSeries EulerMascheroni.Mixed
namespace EulerHarmonic
lemma normalized_coeff (n : ℕ) :
    (n.factorial:ℂ)*coeff n formalExpEin = (harmonic n:ℂ) := by
  induction n with
  | zero => simp [formalExpEin,formalEin,einCoefficient]
  | succ n ih =>
    have h := congrArg (coeff (n+1)) (formal_e_system_equations.2.2)
    simp only [coeff_succ_X_mul,coeff_derivative,map_sub,map_add,coeff_exp,coeff_one,
      Nat.succ_ne_zero,if_false,sub_zero] at h
    rw [harmonic_succ]
    push_cast at h ⊢
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one] at h ⊢
    have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp at h ⊢
    have hfn : (n.factorial:ℂ)*(n.factorial:ℂ)⁻¹=1 :=
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    linear_combination (n.factorial:ℂ)*h + ((n:ℂ)+1)*ih + hfn
end EulerHarmonic


theorem solution (n : ℕ) :
    (n.factorial:ℂ)*PowerSeries.coeff n EulerMascheroni.Mixed.formalExpEin = (harmonic n:ℂ) := by
  exact EulerHarmonic.normalized_coeff n

#print axioms solution
