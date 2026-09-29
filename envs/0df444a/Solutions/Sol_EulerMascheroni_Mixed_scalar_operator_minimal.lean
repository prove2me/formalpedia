-- Prove2me | solution 1 for EulerMascheroni.Mixed.scalar_operator_minimal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T19:46:49.38235+00:00
-- url     : https://prove2.me/submissions/2e023c50-e11d-406f-95fc-e1ef629a7252

import Definitions.Def_eulerScalarEquation
import Theorems.Thm_EulerMascheroni_Mixed_formal_e_system_equations
import Theorems.Thm_EulerMascheroni_Mixed_formal_e_functional_independence
set_option linter.unusedSimpArgs false
open ArithmeticE Polynomial PowerSeries
open EulerMascheroni.Mixed
namespace EulerCyclic
local notation "D" => PowerSeries.derivative ℂ
local notation "E" => PowerSeries.exp ℂ
local notation "A" => EulerMascheroni.Mixed.formalExpEin
local notation "x" => (PowerSeries.X : PowerSeries ℂ)

lemma cast_two : ((2 : Polynomial ℂ) : PowerSeries ℂ) = 2 :=
  map_natCast (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ) 2
lemma cast_three : ((3 : Polynomial ℂ) : PowerSeries ℂ) = 3 :=
  map_natCast (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ) 3

lemma jets (a b c : ℂ) :
    let F := PowerSeries.C a + PowerSeries.C b * E + PowerSeries.C c * A
    x * D F = -PowerSeries.C c + (PowerSeries.C b*x+PowerSeries.C c)*E + PowerSeries.C c*x*A ∧
    x^2 * D (D F) = PowerSeries.C c*(1-x) +
      (PowerSeries.C b*x^2+2*PowerSeries.C c*x-PowerSeries.C c)*E + PowerSeries.C c*x^2*A ∧
    x^3 * D (D (D F)) = PowerSeries.C c*(-x^2+x-2) +
      (PowerSeries.C b*x^3+3*PowerSeries.C c*x^2-3*PowerSeries.C c*x+2*PowerSeries.C c)*E + PowerSeries.C c*x^3*A := by
  dsimp only
  generalize hF : PowerSeries.C a + PowerSeries.C b * E + PowerSeries.C c * A = F
  have he := EulerMascheroni.Mixed.formal_e_system_equations.1
  have ha := EulerMascheroni.Mixed.formal_e_system_equations.2.2
  have h1 : x * D (F) =
      -PowerSeries.C c + (PowerSeries.C b*x+PowerSeries.C c)*E + PowerSeries.C c*x*A := by
    rw [← hF]
    simp only [map_add, Derivation.leibniz, PowerSeries.derivative_C, zero_mul, add_zero, zero_add, he, smul_eq_mul]
    linear_combination PowerSeries.C c * ha
  refine ⟨h1, ?_⟩
  have h2 := congrArg D h1
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, PowerSeries.derivative_C, PowerSeries.derivative_X,
    zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one, he, smul_eq_mul] at h2
  have h2' : x^2 * D (D (F)) =
      PowerSeries.C c*(1-x) + (PowerSeries.C b*x^2+2*PowerSeries.C c*x-PowerSeries.C c)*E + PowerSeries.C c*x^2*A := by
    linear_combination x*h2 - h1 + PowerSeries.C c*x*ha
  refine ⟨h2', ?_⟩
  have htwo : D (2 : PowerSeries ℂ) = 0 := by simpa using Derivation.map_natCast D 2
  have h3 := congrArg D h2'
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, PowerSeries.derivative_C, PowerSeries.derivative_X,
    Derivation.map_one_eq_zero, htwo, Derivation.leibniz_pow,
    zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one, he, smul_eq_mul] at h3
  linear_combination x*h3 - 2*h2' + PowerSeries.C c*x^2*ha

lemma first_three_independent (a b c : ℂ) (hc : c ≠ 0)
    (u v w : Polynomial ℂ)
    (h : (u : PowerSeries ℂ)*formalCombination a b c +
      (v : PowerSeries ℂ)*D (formalCombination a b c) +
      (w : PowerSeries ℂ)*D (D (formalCombination a b c)) = 0) :
    u = 0 ∧ v = 0 ∧ w = 0 := by
  obtain ⟨h1,h2,h3⟩ := jets a b c
  let R := u*Polynomial.C a*Polynomial.X^2-v*Polynomial.C c*Polynomial.X+
    w*Polynomial.C c*(1-Polynomial.X)
  let S := u*Polynomial.C b*Polynomial.X^2+v*(Polynomial.C b*Polynomial.X^2+Polynomial.C c*Polynomial.X)+
    w*(Polynomial.C b*Polynomial.X^2+2*Polynomial.C c*Polynomial.X-Polynomial.C c)
  let U := Polynomial.C c*Polynomial.X^2*(u+v+w)
  have hr : (R : PowerSeries ℂ)+(S : PowerSeries ℂ)*E+(U : PowerSeries ℂ)*A = 0 := by
    dsimp [R,S,U]
    push_cast
    norm_num only [cast_two,cast_three]
    dsimp only [formalCombination] at h
    linear_combination x^2*h - (v : PowerSeries ℂ)*x*h1 - (w : PowerSeries ℂ)*h2
  obtain ⟨hR,hS,hU⟩ := formal_e_functional_independence R S U hr
  have hc' : Polynomial.C c ≠ 0 := by simpa using hc
  have hx : (Polynomial.X : Polynomial ℂ) ≠ 0 := Polynomial.X_ne_zero
  have hsum : u+v+w=0 := (mul_eq_zero.mp hU).resolve_left (mul_ne_zero hc' (pow_ne_zero 2 hx))
  have hlin : Polynomial.X*v+(2*Polynomial.X-1)*w=0 := by
    apply (mul_eq_zero.mp (show Polynomial.C c * (Polynomial.X*v+(2*Polynomial.X-1)*w)=0 from ?_)).resolve_left hc'
    dsimp [S] at hS
    linear_combination hS - Polynomial.C b*Polynomial.X^2*hsum
  have hlast : Polynomial.X*(Polynomial.C a*Polynomial.X-Polynomial.C a+Polynomial.C c)*w=0 := by
    dsimp [R] at hR
    linear_combination hR - Polynomial.C a*Polynomial.X^2*hsum + (Polynomial.C a*Polynomial.X+Polynomial.C c)*hlin
  have hfactor : Polynomial.C a*Polynomial.X-Polynomial.C a+Polynomial.C c ≠ 0 := by
    intro hz
    have he := congrArg (fun p : Polynomial ℂ => p.eval 1) hz
    apply hc
    simpa using he
  have hw : w=0 := (mul_eq_zero.mp hlast).resolve_left (mul_ne_zero hx hfactor)
  have hv : v=0 := (mul_eq_zero.mp (by simpa [hw] using hlin)).resolve_left hx
  exact ⟨by simpa [hv,hw] using hsum,hv,hw⟩


lemma scalar_annihilates (a b c : ℂ) :
    operatorValue (scalarOperator a c) 3 (formalCombination a b c) = 0 := by
  obtain ⟨h1,h2,h3⟩ := jets a b c
  have hx : x^2 ≠ 0 := pow_ne_zero 2 PowerSeries.X_ne_zero
  apply (mul_eq_zero.mp (show x^2 * operatorValue (scalarOperator a c) 3 (formalCombination a b c)=0 from ?_)).resolve_left hx
  norm_num only [operatorValue, scalarOperator, Finset.sum_range_succ,
    Finset.sum_range_zero, Function.iterate_succ_apply', Function.iterate_zero_apply,
    formalCombination, Polynomial.coe_zero, zero_mul, add_zero, zero_add]
  push_cast
  norm_num only [cast_two,cast_three]
  linear_combination
    (PowerSeries.C a*x^2-2*PowerSeries.C a*x+2*PowerSeries.C a+PowerSeries.C c*x-3*PowerSeries.C c)*x*h1 +
    (-2*PowerSeries.C a*x^2+3*PowerSeries.C a*x-2*PowerSeries.C a-2*PowerSeries.C c*x+2*PowerSeries.C c)*h2 +
    (PowerSeries.C a*x-PowerSeries.C a+PowerSeries.C c)*h3

lemma scalar_leading (a c : ℂ) : (scalarOperator a c 3).eval 1 = c := by
  simp [scalarOperator]

lemma scalar_minimal (a b c : ℂ) (hc : c ≠ 0) :
    MinimalEquation (scalarOperator a c) 3 (formalCombination a b c) ∧
      (scalarOperator a c 3).eval 1 ≠ 0 := by
  have hp : scalarOperator a c 3 ≠ 0 := by
    intro h
    have h' := congrArg (fun p : Polynomial ℂ => p.eval 1) h
    apply hc
    simpa [scalar_leading] using h'
  refine ⟨⟨hp,scalar_annihilates a b c,?_⟩, by simpa [scalar_leading] using hc⟩
  intro k hk q hq hz
  interval_cases k
  · have hh := first_three_independent a b c hc (q 0) 0 0
    apply hq
    apply (hh ?_).1
    simpa [operatorValue] using hz
  · have hh := first_three_independent a b c hc (q 0) (q 1) 0
    apply hq
    apply (hh ?_).2.1
    simpa [operatorValue,Finset.sum_range_succ,Function.iterate_succ_apply'] using hz
  · have hh := first_three_independent a b c hc (q 0) (q 1) (q 2)
    apply hq
    apply (hh ?_).2.2
    simpa [operatorValue,Finset.sum_range_succ,Function.iterate_succ_apply'] using hz



end EulerCyclic


theorem solution (a b c : ℂ) (hc : c ≠ 0) :
    MinimalEquation (scalarOperator a c) 3 (formalCombination a b c) ∧
      (scalarOperator a c 3).eval 1 ≠ 0 := by
  exact EulerCyclic.scalar_minimal a b c hc
#print axioms solution
