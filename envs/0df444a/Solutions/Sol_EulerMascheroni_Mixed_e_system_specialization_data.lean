-- Prove2me | solution 1 for EulerMascheroni.Mixed.e_system_specialization_data
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:53:40.235404+00:00
-- url     : https://prove2.me/submissions/cdb46d0f-a026-4b70-a93f-7bf809940d54

import Definitions.Def_rationalEArithmetic
import Definitions.Def_eulerMascheroni_formalESystem
import Theorems.Thm_EulerMascheroni_Mixed_mixed_value_coefficient_sum
import Theorems.Thm_EulerMascheroni_Mixed_formal_e_system_equations
open ArithmeticE PowerSeries EulerMascheroni.Mixed
namespace EulerSpecialization
lemma basis_differential : ∀ i : Fin 3,
    (PowerSeries.X:PowerSeries ℂ)*PowerSeries.derivative ℂ
      (![1,PowerSeries.exp ℂ,formalExpEin] i) =
    ∑ j : Fin 3, (((!![0,0,0;0,Polynomial.X,0;-1,1,Polynomial.X] : Matrix (Fin 3) (Fin 3) (Polynomial ℚ)) i j).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
      (![1,PowerSeries.exp ℂ,formalExpEin] j) := by
  intro i; fin_cases i <;> simp [Fin.sum_univ_succ,formal_e_system_equations.1]
  exact formal_e_system_equations.2.2.trans (by ring)

lemma coeff_expEin (n : ℕ) : coeff n formalExpEin = valueCoefficient 0 0 1 n := by
  simp only [formalExpEin,formalEin,valueCoefficient,PowerSeries.coeff_mul,coeff_exp,
    Rat.cast_zero,Complex.ofReal_zero,Complex.ofReal_one,ite_self,zero_div,
    zero_add,one_mul,PowerSeries.coeff_mk,one_div]
  push_cast
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l =>
    (k.factorial:ℂ)⁻¹*einCoefficient l) n

lemma values_basis : ∀ i : Fin 3,
    seriesValue (![1,PowerSeries.exp ℂ,formalExpEin] i) 1 =
      (![1,Complex.exp 1,expEin 1] i) := by
  intro i; fin_cases i
  · simp [seriesValue]
  · have h := (mixed_value_coefficient_sum 0 1 0).1.tsum_eq
    simpa [seriesValue,valueCoefficient,coeff_exp,one_div] using h
  · have h := (mixed_value_coefficient_sum 0 0 1).1.tsum_eq
    simpa [seriesValue,coeff_expEin] using h

end EulerSpecialization

theorem solution :
    (∀ i : Fin 3,
    (PowerSeries.X:PowerSeries ℂ)*PowerSeries.derivative ℂ
      (![1,PowerSeries.exp ℂ,formalExpEin] i) =
    ∑ j : Fin 3, (((!![0,0,0;0,Polynomial.X,0;-1,1,Polynomial.X] : Matrix (Fin 3) (Fin 3) (Polynomial ℚ)) i j).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
      (![1,PowerSeries.exp ℂ,formalExpEin] j)) ∧
    (∀ i : Fin 3,
    seriesValue (![1,PowerSeries.exp ℂ,formalExpEin] i) 1 =
      (![1,Complex.exp 1,expEin 1] i)) := by
  exact ⟨EulerSpecialization.basis_differential,EulerSpecialization.values_basis⟩

#print axioms solution
