-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_inverse_exact
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:34:32.722068+00:00
-- url     : https://prove2.me/submissions/5229f616-745a-4ad8-9f39-9e6433052dd2

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthOcticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_denominator_bound
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators











theorem sixth_octic_sqrt_remainder_identity (u : ℂ) :
    sixthOcticRadicand u-(sixthOcticPoly u)^2=u^21*sixthOcticResidual u := by
  norm_num [sixthOcticRadicand,sixthOcticPoly,sixthOcticResidual,sixthOcticCoeffs,sixthOcticResidualCoeffs,Fin.sum_univ_succ]
  ring

theorem sixth_octic_expansion_identity (u : ℂ) :
    (91/1360)-(13/48)*u+(17/96)*u^2-((3*Real.sqrt 429/1360:ℝ):ℂ)*sixthOcticPoly u-
      ((((91-3*Real.sqrt 429)/1360:ℝ):ℂ)-((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)*u)*(1-(17/33)*u)=
    u^2*((1-(17/33)*u)*(∑ i : Fin 19,(sixthOcticExpansionCoeffs i:ℂ)*u^i.val)+
      u^19*(sixthOcticRationalTailCoeff:ℂ)) := by
  norm_num [sixthOcticPoly,sixthOcticCoeffs,sixthOcticExpansionCoeffs,sixthOcticRationalTailCoeff,Fin.sum_univ_succ]
  push_cast
  ring








end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace DerivativeChainPrivate











theorem sixth_octic_pole_bound (u : ℂ) (hu : ‖u‖≤3/10) :
    1-(17/33:ℂ)*u≠0 ∧ ‖(1-(17/33:ℂ)*u)⁻¹‖≤6/5 := by
  have hn:=norm_sub_norm_le (1:ℂ) ((17/33:ℂ)*u)
  norm_num [norm_mul] at hn
  have hl : (5/6:ℝ)≤‖1-(17/33:ℂ)*u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi:=inv_anti₀ (by norm_num : (0:ℝ)<5/6) hl
  norm_num at hi
  exact hi
end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem sixth_octic_sqrt_exact_remainder (u : ℂ) (hu : ‖u‖≤3/10) :
    Complex.sqrt (sixthOcticRadicand u)=sixthOcticPoly u+
      u^21*sixthOcticResidual u/(Complex.sqrt (sixthOcticRadicand u)+sixthOcticPoly u) := by
  have hd:=(sixth_octic_denominator_bound u hu).1
  have hs : (Complex.sqrt (sixthOcticRadicand u))^2=sixthOcticRadicand u :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ)≠0)
  have he : (Complex.sqrt (sixthOcticRadicand u)-sixthOcticPoly u)*
      (Complex.sqrt (sixthOcticRadicand u)+sixthOcticPoly u)=u^21*sixthOcticResidual u := by
    calc
      _=(Complex.sqrt (sixthOcticRadicand u))^2-(sixthOcticPoly u)^2 := by ring
      _=_ := by rw [hs,sixth_octic_sqrt_remainder_identity]
  have hh:=(eq_div_iff hd).mpr he
  linear_combination hh

theorem sixth_octic_polynomial_error_identity (w : ℂ) :
    (sixthOcticLeadingError:ℂ)*w+sixthOcticPolynomialError w=
      w*(∑ i : Fin 19,(sixthOcticExpansionCoeffs i:ℂ)*(w^2)^i.val) := by
  norm_num [sixthOcticLeadingError,sixthOcticPolynomialError,sixthOcticErrorCoeffs,Fin.sum_univ_succ]
  ring

theorem sixth_octic_remainder_scaled (w : ℂ) (hw : ‖w^2‖≤3/10) :
    w^3*(1-(17/33)*w^2)*((sixthOcticLeadingError:ℂ)*w+sixthOcticError w)=
      (91/1360)-(13/48)*w^2+(17/96)*w^4-
      ((3*Real.sqrt 429/1360:ℝ):ℂ)*Complex.sqrt (sixthOcticRadicand (w^2))-
      ((((91-3*Real.sqrt 429)/1360:ℝ):ℂ)-((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)*w^2)*(1-(17/33)*w^2) := by
  have hp:=(sixth_octic_pole_bound (w^2) hw).1
  have hs:=sixth_octic_sqrt_exact_remainder (w^2) hw
  have he : Complex.sqrt (sixthOcticRadicand (w^2))-sixthOcticPoly (w^2)=
      (w^2)^21*sixthOcticResidual (w^2)/(Complex.sqrt (sixthOcticRadicand (w^2))+sixthOcticPoly (w^2)) := by
    linear_combination hs
  have htail : (1-(17/33:ℂ)*w^2)*sixthOcticTail w=
      (sixthOcticRationalTailCoeff:ℂ)*w^39-
      ((3*Real.sqrt 429/1360:ℝ):ℂ)*w^39*sixthOcticResidual (w^2)/
        (Complex.sqrt (sixthOcticRadicand (w^2))+sixthOcticPoly (w^2)) := by
    unfold sixthOcticTail
    rw [mul_sub,←mul_div_assoc,←mul_div_assoc,mul_div_cancel_left₀ _ hp,mul_div_cancel_left₀ _ hp]
  calc
    _=(w^2)^2*((1-(17/33)*w^2)*(∑ i : Fin 19,(sixthOcticExpansionCoeffs i:ℂ)*(w^2)^i.val)+
        (w^2)^19*(sixthOcticRationalTailCoeff:ℂ))-
      ((3*Real.sqrt 429/1360:ℝ):ℂ)*(Complex.sqrt (sixthOcticRadicand (w^2))-sixthOcticPoly (w^2)) := by
      unfold sixthOcticError
      rw [←add_assoc,sixth_octic_polynomial_error_identity,he]
      linear_combination w^3*htail
    _=_ := by linear_combination -(sixth_octic_expansion_identity (w^2))


end DerivativeChainPrivate

theorem solution (z : ℂ) (hz : z≠0) (hn : ‖z⁻¹‖^2≤1/4) :
    (((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z=
      ((91/1360)*z^4-(13/48)*z^2+17/96-
        ((3*Real.sqrt 429/1360:ℝ):ℂ)*z^4*Complex.sqrt (sixthOcticRadicand ((z⁻¹)^2)))/(z^2-17/33) := by
  have hw : ‖(z⁻¹)^2‖≤3/10 := by rw [norm_pow]; linarith
  have hp:=(sixth_octic_pole_bound ((z⁻¹)^2) hw).1
  have hzpole : z^2-(17/33:ℂ)≠0 := by
    intro he
    apply hp
    field_simp
    linear_combination (33:ℂ)*he
  have hS:=sixth_octic_remainder_scaled z⁻¹ hw
  change (z⁻¹)^3*(1-(17/33)*(z⁻¹)^2)*sixthOcticRemainder z=_ at hS
  apply (eq_div_iff hzpole).mpr
  calc
    _=((((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z)*(z^2-17/33)-
      z^4*((z⁻¹)^3*(1-(17/33)*(z⁻¹)^2)*sixthOcticRemainder z-
        ((91/1360)-(13/48)*(z⁻¹)^2+(17/96)*(z⁻¹)^4-
          ((3*Real.sqrt 429/1360:ℝ):ℂ)*Complex.sqrt (sixthOcticRadicand ((z⁻¹)^2))-
          ((((91-3*Real.sqrt 429)/1360:ℝ):ℂ)-((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)*(z⁻¹)^2)*(1-(17/33)*(z⁻¹)^2))) := by
      rw [hS]
      ring
    _=_ := by field_simp; ring
