-- Prove2me | solution 1 for EulerMascheroni.Mixed.e_system_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:53:39.743274+00:00
-- url     : https://prove2.me/submissions/c375125c-7b98-46a2-9cdf-012b63893115

import Definitions.Def_rationalEArithmetic
import Theorems.Thm_EulerMascheroni_Mixed_formal_expEin_harmonic_coefficients
import Theorems.Thm_ArithmeticE_harmonic_arithmetic
open ArithmeticE PowerSeries EulerMascheroni.Mixed
namespace EulerSpecialization

lemma arithmetic_one : RationalSeriesArithmetic (1:PowerSeries ℂ) := by
  refine ⟨fun n => if n=0 then 1 else 0, ?_, 1,by norm_num,?_,?_⟩
  · intro n; by_cases hn:n=0 <;> simp [hn]
  · intro n; by_cases h:n=0 <;> simp [h]
  · intro n; refine ⟨1,by norm_num,by norm_num,?_⟩
    intro k hk; by_cases h:k=0
    · exact ⟨1,by simp [h]⟩
    · exact ⟨0,by simp [h]⟩

lemma arithmetic_exp : RationalSeriesArithmetic (PowerSeries.exp ℂ) := by
  refine ⟨fun _ => 1, ?_, 1,by norm_num,?_,?_⟩
  · intro n; simp [coeff_exp, Nat.factorial_ne_zero]
  · intro n; norm_num
  · intro n; exact ⟨1,by norm_num,by norm_num,fun k hk => ⟨1,by norm_num⟩⟩

lemma arithmetic_expEin : RationalSeriesArithmetic formalExpEin :=
  ⟨harmonic,formal_expEin_harmonic_coefficients,ArithmeticE.harmonic_arithmetic⟩

lemma arithmetic_basis : ∀ i : Fin 3,
    RationalSeriesArithmetic (![1, PowerSeries.exp ℂ, formalExpEin] i) := by
  intro i; fin_cases i
  · exact arithmetic_one
  · exact arithmetic_exp
  · exact arithmetic_expEin


end EulerSpecialization


theorem solution : ∀ i : Fin 3,
    RationalSeriesArithmetic (![1, PowerSeries.exp ℂ, formalExpEin] i) := by
  exact EulerSpecialization.arithmetic_basis

#print axioms solution
