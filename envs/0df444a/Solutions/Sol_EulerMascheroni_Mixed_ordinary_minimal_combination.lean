-- Prove2me | solution 1 for EulerMascheroni.Mixed.ordinary_minimal_combination
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T19:46:50.245009+00:00
-- url     : https://prove2.me/submissions/d220f5b7-1278-4a3e-8520-eae8fc54c6b2

import Definitions.Def_eulerScalarEquation
import Theorems.Thm_EulerMascheroni_Mixed_formal_e_system_equations
import Theorems.Thm_EulerMascheroni_Mixed_formal_e_functional_independence
import Theorems.Thm_EulerMascheroni_Mixed_scalar_operator_minimal
open ArithmeticE Polynomial PowerSeries EulerMascheroni.Mixed
namespace EulerCyclic
local notation "D" => PowerSeries.derivative ℂ
local notation "E" => PowerSeries.exp ℂ
local notation "A" => EulerMascheroni.Mixed.formalExpEin
lemma combination_ne_zero (a b c : ℂ) (hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    formalCombination a b c ≠ 0 := by
  intro hz
  have hh : ((Polynomial.C a : Polynomial ℂ) : PowerSeries ℂ) +
      ((Polynomial.C b : Polynomial ℂ) : PowerSeries ℂ)*E+
      ((Polynomial.C c : Polynomial ℂ) : PowerSeries ℂ)*A=0 := by simpa [formalCombination] using hz
  obtain ⟨h0,h1,h2⟩ := formal_e_functional_independence _ _ _ hh
  have ha : a=0 := by simpa using h0
  have hb : b=0 := by simpa using h1
  have hc : c=0 := by simpa using h2
  tauto

lemma first_order_minimal (F : PowerSeries ℂ) (hF : F ≠ 0) (p : Polynomial ℂ)
    (h : (p : PowerSeries ℂ)*F+D F=0) :
    MinimalEquation (fun n => if n=0 then p else 1) 1 F := by
  refine ⟨by simp, ?_, ?_⟩
  · simpa [operatorValue,Finset.sum_range_succ] using h
  · intro k hk q hq hz
    have hk0 : k=0 := by omega
    subst k
    have hmul : (q 0 : PowerSeries ℂ)*F=0 := by simpa [operatorValue] using hz
    exact hq (Polynomial.coe_eq_zero_iff.mp ((mul_eq_zero.mp hmul).resolve_right hF))

lemma two_jets (a b : ℂ) :
    D (formalCombination a b 0) = PowerSeries.C b*E ∧
    D (D (formalCombination a b 0)) = PowerSeries.C b*E := by
  have he := formal_e_system_equations.1
  have hd : D (formalCombination a b 0) = PowerSeries.C b*E := by
    simp [formalCombination,Derivation.leibniz,he]
  refine ⟨hd,?_⟩
  rw [hd]
  simp [Derivation.leibniz,he]

lemma first_two_independent (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (u v : Polynomial ℂ)
    (h : (u : PowerSeries ℂ)*formalCombination a b 0 +
      (v : PowerSeries ℂ)*D (formalCombination a b 0)=0) : u=0 ∧ v=0 := by
  have hr : ((u*Polynomial.C a : Polynomial ℂ) : PowerSeries ℂ)+
      (((u+v)*Polynomial.C b : Polynomial ℂ) : PowerSeries ℂ)*E+(0 : PowerSeries ℂ)*A=0 := by
    rw [(two_jets a b).1] at h
    simp only [formalCombination,map_zero,zero_mul,add_zero] at h
    push_cast
    linear_combination h
  obtain ⟨h0,h1,h2⟩ := formal_e_functional_independence (u*Polynomial.C a) ((u+v)*Polynomial.C b) 0 hr
  have hu : u=0 := (mul_eq_zero.mp h0).resolve_right (by simpa using ha)
  refine ⟨hu,?_⟩
  have hv : u+v=0 := (mul_eq_zero.mp h1).resolve_right (by simpa using hb)
  simpa [hu] using hv

lemma second_order_minimal (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    MinimalEquation (fun n => if n=0 then 0 else if n=1 then -1 else 1) 2 (formalCombination a b 0) := by
  refine ⟨by simp, ?_, ?_⟩
  · simp [operatorValue,Finset.sum_range_succ,Function.iterate_succ_apply',two_jets,formal_e_system_equations.1]
  · intro k hk q hq hz
    interval_cases k
    · apply hq
      apply (first_two_independent a b ha hb (q 0) 0 ?_).1
      simpa [operatorValue] using hz
    · apply hq
      apply (first_two_independent a b ha hb (q 0) (q 1) ?_).2
      simpa [operatorValue,Finset.sum_range_succ] using hz

lemma ordinary_minimal_combination (a b c : ℂ) (hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∃ (p : ℕ → Polynomial ℂ) (n : ℕ), 0 < n ∧
      MinimalEquation p n (formalCombination a b c) ∧ (p n).eval 1 ≠ 0 := by
  by_cases hc : c=0
  · subst c
    by_cases ha : a=0
    · subst a
      refine ⟨(fun n => if n=0 then -1 else 1),1,by norm_num,?_,by simp⟩
      apply first_order_minimal _ (combination_ne_zero _ _ _ hn)
      rw [(two_jets 0 b).1]
      simp [formalCombination]
    · by_cases hb : b=0
      · subst b
        refine ⟨(fun n => if n=0 then 0 else 1),1,by norm_num,?_,by simp⟩
        apply first_order_minimal _ (combination_ne_zero _ _ _ hn)
        rw [(two_jets a 0).1]
        simp
      · exact ⟨_,2,by norm_num,second_order_minimal a b ha hb,by simp⟩
  · exact ⟨_,3,by norm_num,(EulerMascheroni.Mixed.scalar_operator_minimal a b c hc).1,(EulerMascheroni.Mixed.scalar_operator_minimal a b c hc).2⟩

end EulerCyclic


theorem solution (a b c : ℂ) (hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∃ (p : ℕ → Polynomial ℂ) (n : ℕ), 0 < n ∧
      MinimalEquation p n (formalCombination a b c) ∧ (p n).eval 1 ≠ 0 := by
  exact EulerCyclic.ordinary_minimal_combination a b c hn
#print axioms solution
