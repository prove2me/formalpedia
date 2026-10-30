-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_septic_upper_graphs
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:12:55.149097+00:00
-- url     : https://prove2.me/submissions/f4406f94-1a61-4051-9e0b-fd1b8d3e89ef

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthSepticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_SixthSepticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_denominator_bound
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
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators






theorem sixth_septic_remainder_identity (u : ℂ) :
    sixthSepticRadicand u-(sixthSepticPoly u)^2=u^21*sixthSepticResidual u := by
  norm_num [sixthSepticRadicand,sixthSepticPoly,sixthSepticResidual,
    sixthSepticCoeffs,sixthSepticResidualCoeffs,Fin.sum_univ_succ]
  ring




end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators




theorem sixth_septic_sqrt_exact_remainder (u : ℂ) (hu : ‖u‖≤3/8) :
    Complex.sqrt (sixthSepticRadicand u)=sixthSepticPoly u+
      u^21*sixthSepticResidual u/(Complex.sqrt (sixthSepticRadicand u)+sixthSepticPoly u) := by
  have hd:=(sixth_septic_denominator_bound u hu).1
  have hs : (Complex.sqrt (sixthSepticRadicand u))^2=sixthSepticRadicand u :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ)≠0)
  have he : (Complex.sqrt (sixthSepticRadicand u)-sixthSepticPoly u)*
      (Complex.sqrt (sixthSepticRadicand u)+sixthSepticPoly u)=u^21*sixthSepticResidual u := by
    calc
      _=(Complex.sqrt (sixthSepticRadicand u))^2-(sixthSepticPoly u)^2 := by ring
      _=_ := by rw [hs,sixth_septic_remainder_identity]
  have hh:=(eq_div_iff hd).mpr he
  linear_combination hh

theorem sixth_septic_polynomial_error_identity (w : ℂ) :
    w^3*((sixthSepticLeadingError:ℂ)*w+sixthSepticPolynomialError w)=
      (17/192)*w^4-((3*Real.sqrt 15145/2720:ℝ):ℂ)*
        (sixthSepticPoly (w^2)-1+(1309/699)*w^2) := by
  norm_num [sixthSepticLeadingError,sixthSepticPolynomialError,sixthSepticPoly,sixthSepticErrorCoeffs,
    sixthSepticCoeffs,Fin.sum_univ_succ]
  push_cast
  ring

theorem sixth_septic_tail_identity (w : ℂ) (hw : ‖w^2‖≤3/8) :
    w^3*sixthSepticTail w=-((3*Real.sqrt 15145/2720:ℝ):ℂ)*
      (Complex.sqrt (sixthSepticRadicand (w^2))-sixthSepticPoly (w^2)) := by
  have hs:=sixth_septic_sqrt_exact_remainder (w^2) hw
  have he : Complex.sqrt (sixthSepticRadicand (w^2))-sixthSepticPoly (w^2)=
      (w^2)^21*sixthSepticResidual (w^2)/(Complex.sqrt (sixthSepticRadicand (w^2))+sixthSepticPoly (w^2)) := by
    linear_combination hs
  rw [he]
  dsimp only [sixthSepticTail]
  ring

theorem sixth_septic_remainder_exact (z : ℂ) (hz : z≠0) (hn : ‖z⁻¹‖^2≤2/7) :
    sixthSepticRemainder z=(17/192)/z-((3*Real.sqrt 15145/2720:ℝ):ℂ)*z^3*
      (Complex.sqrt (sixthSepticRadicand ((z⁻¹)^2))-1+(1309/699)*(z⁻¹)^2) := by
  have hw : ‖(z⁻¹)^2‖≤3/8 := by rw [norm_pow]; linarith
  have hP:=sixth_septic_polynomial_error_identity z⁻¹
  have hT:=sixth_septic_tail_identity z⁻¹ hw
  have hR : (z⁻¹)^3*sixthSepticRemainder z=(17/192)*(z⁻¹)^4-
      ((3*Real.sqrt 15145/2720:ℝ):ℂ)*(Complex.sqrt (sixthSepticRadicand ((z⁻¹)^2))-1+(1309/699)*(z⁻¹)^2) := by
    dsimp only [sixthSepticRemainder,sixthSepticError]
    linear_combination hP+hT
  apply mul_left_cancel₀ (pow_ne_zero 3 (inv_ne_zero hz))
  rw [hR]
  field_simp <;> ring

theorem sixth_septic_inverse_exact (z : ℂ) (hz : z≠0) (hn : ‖z⁻¹‖^2≤2/7) :
    (((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder z/z=
      (91/544)*z^2-13/32+(17/192)/z^2-
        ((3*Real.sqrt 15145/2720:ℝ):ℂ)*z^2*Complex.sqrt (sixthSepticRadicand ((z⁻¹)^2)) := by
  rw [sixth_septic_remainder_exact z hz hn]
  push_cast
  field_simp <;> ring
end DerivativeChainPrivate

theorem solution (β z : ℂ) (hx : 0<z.re) (hX : 7/2≤z.re^2)
    (hroot : (1360/13)*β^2*z-35*β*z^4+85*β*z^2-(1445/78)*β+
      z^7-7*z^5+(595/48)*z^3-(1445/312)*z=0) :
    β/z=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder z/z ∨
    β/z=(((455+3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
      ((13/32+77*Real.sqrt 15145/37280:ℝ):ℂ)+((17/96)/z-sixthSepticRemainder z)/z := by
  have hz : z≠0 := by intro he; simp [he] at hx
  have hnorm : 7/2≤‖z‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  have hn : ‖z⁻¹‖^2≤2/7 := by
    rw [norm_inv,inv_pow]
    apply (inv_le_comm₀ (by positivity : 0<‖z‖^2) (by norm_num)).mpr
    norm_num
    exact hnorm
  let S:=Complex.sqrt (sixthSepticRadicand ((z⁻¹)^2))
  let s : ℂ := (Real.sqrt 15145:ℂ)
  have hs : s^2=15145 := by
    dsimp [s]
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have hS : S^2=sixthSepticRadicand ((z⁻¹)^2) :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ)≠0)
  have hd : (β*z-(91/544)*z^4+(13/32)*z^2-17/192)^2=
      (136305/7398400)*(z^8-(2618/699)*z^6+(2890/699)*z^4-(122825/81783)*z^2+417605/981396) := by
    linear_combination (13/1360)*z*hroot
  have hsquare : ((3/2720)*s*z^4*S)^2=
      (136305/7398400)*(z^8-(2618/699)*z^6+(2890/699)*z^4-(122825/81783)*z^2+417605/981396) := by
    calc
      _=(9/7398400)*s^2*z^8*S^2 := by ring
      _=_ := by rw [hs,hS]; unfold sixthSepticRadicand; field_simp; ring
  have hsplit:=(sq_eq_sq_iff_eq_or_eq_neg).mp (hd.trans hsquare.symm)
  have hbase : β/z=(91/544)*z^2-13/32+(17/192)/z^2-(3*s/2720)*z^2*S ∨
      β/z=(91/544)*z^2-13/32+(17/192)/z^2+(3*s/2720)*z^2*S := by
    rcases hsplit with hp|hm
    · right
      apply (div_eq_iff hz).mpr
      apply mul_left_cancel₀ hz
      have he : z*((91/544)*z^2-13/32+(17/192)/z^2+(3*s/2720)*z^2*S)*z=
          (91/544)*z^4-(13/32)*z^2+17/192+(3/2720)*s*z^4*S := by field_simp <;> ring
      rw [←mul_assoc,he]
      linear_combination hp
    · left
      apply (div_eq_iff hz).mpr
      apply mul_left_cancel₀ hz
      have he : z*((91/544)*z^2-13/32+(17/192)/z^2-(3*s/2720)*z^2*S)*z=
          (91/544)*z^4-(13/32)*z^2+17/192-(3/2720)*s*z^4*S := by field_simp <;> ring
      rw [←mul_assoc,he]
      linear_combination hm
  have hminus:=sixth_septic_inverse_exact z hz hn
  change _=(91/544)*z^2-13/32+(17/192)/z^2-((3*Real.sqrt 15145/2720:ℝ):ℂ)*z^2*S at hminus
  have hplus : (((455+3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
      ((13/32+77*Real.sqrt 15145/37280:ℝ):ℂ)+((17/96)/z-sixthSepticRemainder z)/z=
      (91/544)*z^2-13/32+(17/192)/z^2+(3*s/2720)*z^2*S := by
    calc
      _=(91/272)*z^2-13/16+(17/96)/z^2-
          ((((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
            ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder z/z) := by
        push_cast
        field_simp
        ring
      _=_ := by rw [hminus]; dsimp only [s]; push_cast; ring
  rcases hbase with hm|hp
  · left
    rw [hminus]
    convert hm using 1 <;> dsimp only [s] <;> push_cast <;> ring
  · right
    rw [hplus]
    exact hp
