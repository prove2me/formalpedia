-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_sextic_upper_graphs
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:52:18.438692+00:00
-- url     : https://prove2.me/submissions/e7b06ee3-8a53-4a48-9938-87d1c3ad2f22

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
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
open Set
namespace DerivativeChainPrivate







theorem sexticUpperBranch_sq (a b c : ℝ) (z : ℂ) :
    (sexticUpperBranch a b c z)^2 = sexticRadicand a b c z := by
  rw [sexticUpperBranch,mul_pow]
  have hs : (Complex.sqrt (-sexticRadicand a b c z))^2 = -sexticRadicand a b c z :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
  rw [hs,Complex.I_sq]
  ring









end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainPrivate
open Polynomial MeasureTheory Set TeschlQM.Herglotz













theorem sixth_sextic_discriminant_identity (β z : ℂ)
    (hroot : (1360/91)*β^2-20*β*z^3+(170/7)*β*z+
      z^6-5*z^4+(85/16)*z^2-1445/2184=0) :
    (1360*β-910*z^3+1105*z)^2=
      704340*z^6-1392300*z^4+563550*z^2+245650/3 := by
  linear_combination 123760*hroot





end DerivativeChainPrivate

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ u : ℂ, 0 <u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u=
      TeschlQM.Herglotz.borelTransform μ u)
    (β z : ℂ) (hx : 0<z.re) (hy : 0<z.im)
    (hroot : (1360/91)*β^2-20*β*z^3+(170/7)*β*z+z^6-5*z^4+(85/16)*z^2-1445/2184=0) :
    let J:=∫ t : ℝ,(z^2-(t:ℂ))⁻¹ ∂μ
    β/z=(((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*z^2-
      (((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+((3*Real.sqrt 19565/680:ℝ):ℂ)*J ∨
    β/z=(((455+3*Real.sqrt 19565)/680:ℝ):ℂ)*z^2-
      (((559+3*Real.sqrt 19565)/688:ℝ):ℂ)-((3*Real.sqrt 19565/680:ℝ):ℂ)*J := by
  let F:=sexticUpperBranch (-85/43) (1445/1806) (24565/211302) (z^2)
  let s : ℂ := (Real.sqrt 19565:ℂ)
  let J:=∫ t : ℝ,(z^2-(t:ℂ))⁻¹ ∂μ
  have hz : z≠0 := by intro h; simp [h] at hx
  have hu : 0<(z^2).im := by simp [pow_two,Complex.mul_im]; positivity
  have hs : s^2=19565 := by dsimp [s]; rw [←Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]; norm_num
  have hF : F^2=z^4+(-85/43:ℂ)*z^2+1445/1806+(24565/211302:ℂ)/z^2 := by
    have ht:=sexticUpperBranch_sq (-85/43) (1445/1806) (24565/211302) (z^2)
    simpa [F,sexticRadicand,←pow_mul] using ht
  have hJ : F=z^2-85/86-J := by
    have ht:=hμ (z^2) hu
    have hi : TeschlQM.Herglotz.borelTransform μ (z^2)=-J := by
      unfold TeschlQM.Herglotz.borelTransform
      dsimp only [J]
      rw [←integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [←neg_sub,inv_neg])
    rw [hi] at ht
    dsimp only [sexticShift] at ht
    norm_num [F] at ht ⊢
    linear_combination ht
  have hd:=sixth_sextic_discriminant_identity β z hroot
  have hsquare : (6*s*z*F)^2=704340*z^6-1392300*z^4+563550*z^2+245650/3 := by
    calc
      _=36*s^2*z^2*F^2 := by ring
      _=_ := by rw [hs,hF]; field_simp; ring
  have hsplit:=(sq_eq_sq_iff_eq_or_eq_neg).mp (hd.trans hsquare.symm)
  dsimp only
  rcases hsplit with hp|hm
  · right
    apply (div_eq_iff hz).mpr
    rw [hJ] at hp
    dsimp only [s] at hp
    push_cast
    linear_combination (1/1360:ℂ)*hp
  · left
    apply (div_eq_iff hz).mpr
    rw [hJ] at hm
    dsimp only [s] at hm
    push_cast
    linear_combination (1/1360:ℂ)*hm
