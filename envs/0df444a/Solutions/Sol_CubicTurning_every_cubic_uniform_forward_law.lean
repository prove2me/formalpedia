-- Prove2me | solution 1 for CubicTurning.every_cubic_uniform_forward_law
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:40:33.818888+00:00
-- url     : https://prove2.me/submissions/3576e80f-4494-4f88-a099-2ce3228371a2

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_CubicTurning_affine_cubic_uniform_law
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning









































































theorem normalize_centered_three (a b c : ℂ) (hcenter : a+b+c=0) :
    ∃ (r : ℝ) (t A B C : ℂ), 0 ≤ r ∧ ‖t‖=1 ∧
      a=t*A ∧ b=t*B ∧ c=t*C ∧ A+B+C=0 ∧
      A^2+B^2+C^2=6*(r:ℂ)^2 := by
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq ((a^2+b^2+c^2)/6) (by decide : 0<2)
  have hm : a^2+b^2+c^2=6*s^2 := by linear_combination -6*hs
  by_cases hz : s=0
  · refine ⟨0,1,a,b,c,le_rfl,by simp,by simp,by simp,by simp,hcenter,?_⟩
    simpa [hz] using hm
  · let r : ℝ := ‖s‖
    have hr : 0<r := norm_pos_iff.mpr hz
    have hr0 : r≠0 := ne_of_gt hr
    have hrC : (r:ℂ)≠0 := by exact_mod_cast hr0
    let t : ℂ := s/(r:ℂ)
    let A := (r:ℂ)*a/s
    let B := (r:ℂ)*b/s
    let C := (r:ℂ)*c/s
    have ht : ‖t‖=1 := by
      dsimp [t]
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
      exact div_self hr0
    refine ⟨r,t,A,B,C,hr.le,ht,?_,?_,?_,?_,?_⟩
    · dsimp [t,A]; field_simp
    · dsimp [t,B]; field_simp
    · dsimp [t,C]; field_simp
    · dsimp [A,B,C]
      have he : (r:ℂ)*a/s+(r:ℂ)*b/s+(r:ℂ)*c/s=(r:ℂ)*(a+b+c)/s := by ring
      rw [he,hcenter]; simp
    · dsimp [A,B,C]
      field_simp
      linear_combination hm







theorem anisotropy_normal_form (r : ℝ) (A B C u t : ℂ)
    (ht : ‖t‖=1) (hcenter : A+B+C=0)
    (hsecond : A^2+B^2+C^2=6*(r:ℂ)^2) :
    centroid (u+t*A) (u+t*B) (u+t*C)=u ∧
    centeredVariance (u+t*A) (u+t*B) (u+t*C)=variance A B C ∧
    anisotropy (u+t*A) (u+t*B) (u+t*C)=2*r^2 := by
  have hcent : centroid (u+t*A) (u+t*B) (u+t*C)=u := by
    unfold centroid
    have he : (u+t*A)+(u+t*B)+(u+t*C)=3*u+t*(A+B+C) := by ring
    rw [he,hcenter]; ring
  refine ⟨hcent,?_,?_⟩
  · simp only [centeredVariance,hcent,add_sub_cancel_left,variance,norm_mul,ht,one_mul]
  · simp only [anisotropy,hcent,add_sub_cancel_left]
    have he : ((t*A)^2+(t*B)^2+(t*C)^2)/3=t^2*((A^2+B^2+C^2)/3) := by ring
    rw [he,hsecond,norm_mul,norm_pow,ht,one_pow,one_mul]
    have hh : 6*(r:ℂ)^2/3=(2*r^2:ℝ) := by push_cast; ring
    rw [hh,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]




























end CubicTurning

open CubicTurning in
/-- Every monic cubic is represented by its three complex root slots, including multiplicity. -/
theorem solution (a b c : ℂ) :
    ∃ L : AffineUniformForwardLaw a b c (centroid a b c),
      L.meanEnergy ≤ (anisotropy a b c +
        Real.sqrt (anisotropy a b c*(2*centeredVariance a b c-anisotropy a b c)))/3 ∧
      L.meanEnergy ≤ (2/3)*centeredVariance a b c := by
  let u := centroid a b c
  have hc : (a-u)+(b-u)+(c-u)=0 := by dsimp [u,centroid]; ring
  clear_value u
  obtain ⟨r,t,A,B,C,hr,ht,ha,hb,hc',hcenter,hsecond⟩ :=
    normalize_centered_three (a-u) (b-u) (c-u) hc
  have hae : a=u+t*A := by linear_combination ha
  have hbe : b=u+t*B := by linear_combination hb
  have hce : c=u+t*C := by linear_combination hc'
  obtain ⟨L,h₀,h₁⟩ := affine_cubic_uniform_law r A B C u t hr ht hcenter hsecond
  obtain ⟨hcent,hvar,haniso⟩ := anisotropy_normal_form r A B C u t ht hcenter hsecond
  subst a b c
  rw [hcent,hvar,haniso]
  exact ⟨L,h₀,h₁⟩
