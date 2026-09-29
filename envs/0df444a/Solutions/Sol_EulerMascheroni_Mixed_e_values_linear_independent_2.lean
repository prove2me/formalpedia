-- Prove2me | solution 2 for EulerMascheroni.Mixed.e_values_linear_independent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T19:50:23.770985+00:00
-- url     : https://prove2.me/submissions/c6467ada-7c19-4d8c-afc0-c11c04454637
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_Mixed_ordinary_minimal_combination
import Theorems.Thm_ArithmeticE_algebraic_e_combination_zero_singularity
import Theorems.Thm_EulerMascheroni_Mixed_e_system_arithmetic
import Theorems.Thm_EulerMascheroni_Mixed_e_system_specialization_data
open ArithmeticE PowerSeries EulerMascheroni.Mixed
namespace EulerCyclicApplication
lemma values_independent (a b c : ℝ) (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b)
    (hc : IsAlgebraic ℚ c)
    (h : (a : ℂ)+(b : ℂ)*Complex.exp 1+(c : ℂ)*expEin 1=0) :
    a=0 ∧ b=0 ∧ c=0 := by
  classical
  by_contra hn
  have hn' : (a : ℂ) ≠ 0 ∨ (b : ℂ) ≠ 0 ∨ (c : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_ne_zero] using (show a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 by tauto)
  obtain ⟨p,n,hnpos,hmin,hpn⟩ := ordinary_minimal_combination a b c hn'
  let f : Fin 3 → PowerSeries ℂ := ![1,PowerSeries.exp ℂ,formalExpEin]
  let P : Fin 3 → Polynomial ℂ := ![Polynomial.C (a : ℂ),Polynomial.C (b : ℂ),Polynomial.C (c : ℂ)]
  have ha' : IsAlgebraic ℚ (a : ℂ) :=
    (isAlgebraic_algebraMap_iff (R := ℚ) (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr ha
  have hb' : IsAlgebraic ℚ (b : ℂ) :=
    (isAlgebraic_algebraMap_iff (R := ℚ) (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr hb
  have hc' : IsAlgebraic ℚ (c : ℂ) :=
    (isAlgebraic_algebraMap_iff (R := ℚ) (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr hc
  have hP : ∀ i k, IsAlgebraic ℚ ((P i).coeff k) := by
    intro i k
    fin_cases i <;> by_cases hk : k=0 <;> simp [P,Polynomial.coeff_C,hk,ha',hb',hc',isAlgebraic_zero]
  have hval : ∑ i, (P i).eval 1 * seriesValue (f i) 1=0 := by
    simp only [f,e_system_specialization_data.2]
    simpa [P,Fin.sum_univ_succ,add_assoc] using h
  have hsum : (∑ i, (P i : PowerSeries ℂ)*f i)=formalCombination a b c := by
    simp [P,f,Fin.sum_univ_succ,formalCombination,add_assoc]
  apply hpn
  exact algebraic_e_combination_zero_singularity 3 f e_system_arithmetic P hP 1
    isAlgebraic_one one_ne_zero hval p n hnpos (by simpa only [hsum] using hmin)
end EulerCyclicApplication


theorem solution
    (a b c : ℝ) (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b)
    (hc : IsAlgebraic ℚ c)
    (h : (a : ℂ) + (b : ℂ) * Complex.exp 1 +
      (c : ℂ) * EulerMascheroni.Mixed.expEin 1 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  exact EulerCyclicApplication.values_independent a b c ha hb hc h
#print axioms solution
