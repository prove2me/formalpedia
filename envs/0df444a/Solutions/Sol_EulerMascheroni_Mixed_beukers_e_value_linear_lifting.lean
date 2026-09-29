-- Prove2me | solution 1 for EulerMascheroni.Mixed.beukers_e_value_linear_lifting
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:53:43.782842+00:00
-- url     : https://prove2.me/submissions/ac7a710f-a750-464b-9a0a-972c0f422644
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ArithmeticE_beukers_rational_system_lifting
import Theorems.Thm_EulerMascheroni_Mixed_e_system_arithmetic
import Theorems.Thm_EulerMascheroni_Mixed_e_system_specialization_data
open ArithmeticE PowerSeries EulerMascheroni.Mixed

theorem solution (a b c : ℝ) (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b)
    (hc : IsAlgebraic ℚ c)
    (h : (a:ℂ)+(b:ℂ)*Complex.exp 1+(c:ℂ)*expEin 1=0) :
    ∃ p q r : Polynomial ℂ,
      (p:PowerSeries ℂ)+(q:PowerSeries ℂ)*PowerSeries.exp ℂ+
        (r:PowerSeries ℂ)*formalExpEin=0 ∧
      p.eval 1=(a:ℂ) ∧ q.eval 1=(b:ℂ) ∧ r.eval 1=(c:ℂ) := by
  have halg : ∀ i : Fin 3, IsAlgebraic ℚ (![(a:ℂ),(b:ℂ),(c:ℂ)] i) := by
    intro i; fin_cases i
    · exact (isAlgebraic_algebraMap_iff (R := ℚ) (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr ha
    · exact (isAlgebraic_algebraMap_iff (R := ℚ) (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr hb
    · exact (isAlgebraic_algebraMap_iff (R := ℚ) (FaithfulSMul.algebraMap_injective ℝ ℂ)).mpr hc
  have hrel : ∑ i : Fin 3, (![(a:ℂ),(b:ℂ),(c:ℂ)] i)*
      seriesValue (![1,PowerSeries.exp ℂ,formalExpEin] i) 1=0 := by
    simpa [(EulerMascheroni.Mixed.e_system_specialization_data.2),Fin.sum_univ_succ,add_assoc] using h
  obtain ⟨p,hp,heval⟩ := ArithmeticE.beukers_rational_system_lifting 3
    ![1,PowerSeries.exp ℂ,formalExpEin] Polynomial.X
    !![0,0,0;0,Polynomial.X,0;-1,1,Polynomial.X]
    EulerMascheroni.Mixed.e_system_arithmetic (by simpa using EulerMascheroni.Mixed.e_system_specialization_data.1)
    1 (isAlgebraic_one) (by simp)
    ![(a:ℂ),(b:ℂ),(c:ℂ)] halg hrel
  refine ⟨p 0,p 1,p 2,?_,heval 0,heval 1,heval 2⟩
  simpa [Fin.sum_univ_succ,add_assoc] using hp

#print axioms solution
