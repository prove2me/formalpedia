-- Prove2me | solution 1 for DerivativeChainContinuation.selected_sixth_octic_unit_interface
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:06:58.202567+00:00
-- url     : https://prove2.me/submissions/330ea271-1715-4c29-a6b7-69bf8f250e44

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SixthPhysicalNormalization
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_sixth_actual_rows_to_physical
import Theorems.Thm_DerivativeChainContinuation_sixth_physical_parameter_dictionary
import Theorems.Thm_DerivativeChainContinuation_sixth_physical_parameter_quadrant
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_remainder_bounds
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_selected_bounds
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
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate





theorem sixth_prefix_radius_positive : 0<sixthPrefixRadius := by
  unfold sixthPrefixRadius
  positivity

theorem sixth_prefix_radius_sq : sixthPrefixRadius^2=17/2 :=
  Real.sq_sqrt (by norm_num)

theorem sixth_physical_scale_sq : sixthPhysicalScale^2=2/17 := by
  unfold sixthPhysicalScale
  rw [div_pow,sixth_prefix_radius_sq]
  norm_num



theorem sixth_physical_scale_positive : 0<sixthPhysicalScale := by
  unfold sixthPhysicalScale
  exact one_div_pos.mpr sixth_prefix_radius_positive















end DerivativeChainContinuation

theorem solution (β w : ℂ) (hR : 0≤β.re) (hI : 0<β.im)
    (hx : 0<w.re) (hy : 0<w.im) (hX : 4≤w.re^2)
    (hactual : (derivative^[10] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval w=0)
    (hgraph : β/w=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*w^2-
      ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder w/w) :
    let c:=sixthPhysicalScale
    let γ:=sixthPhysicalParameter β
    let v:=(c:ℂ)*w
    let E:=((16*c:ℝ):ℂ)*sixthOcticRemainder w
    0≤γ.re ∧ 0<γ.im ∧ 0<v.re ∧ 0<v.im ∧ 52/85<v.re^2 ∧
      (derivative^[10] ((X^3-X-C γ)^6 : Polynomial ℂ)).eval v=0 ∧
      γ/v=(((91-3*Real.sqrt 429)/10:ℝ):ℂ)*v^2-
        ((208/55-54*Real.sqrt 429/605:ℝ):ℂ)+E/v ∧
      0<E.re/v.re ∧ E.re/v.re≤18/125 ∧ E.im/v.im≤0 ∧
      0≤(3*(E.re/v.re)-E.im/v.im)/2 ∧ (3*(E.re/v.re)-E.im/v.im)/2≤73/250 ∧
      52/85≤v.re^2-3*v.im^2 := by
  let c:=sixthPhysicalScale
  let γ:=sixthPhysicalParameter β
  let v:=(c:ℂ)*w
  let E:=((16*c:ℝ):ℂ)*sixthOcticRemainder w
  have hc : 0<c := sixth_physical_scale_positive
  have hc0 : c≠0 := hc.ne'
  have hcc : (c:ℂ)≠0 := by exact_mod_cast hc0
  have hc2 : c^2=2/17 := sixth_physical_scale_sq
  have hcc2 : (c:ℂ)^2=2/17 := by rw [←Complex.ofReal_pow,hc2]; norm_num
  have hw : w≠0 := by intro he; simp [he] at hx
  have hx0 : w.re≠0 := hx.ne'
  have hy0 : w.im≠0 := hy.ne'
  have hγ : γ=((16*c:ℝ):ℂ)*β := by
    dsimp [γ]
    rw [sixth_physical_parameter_dictionary]
    change 136*(c:ℂ)^3*β=((16*c:ℝ):ℂ)*β
    push_cast
    calc
      _=136*(c:ℂ)^2*(c:ℂ)*β := by ring
      _=_ := by rw [hcc2]; ring
  obtain ⟨hγR,hγI⟩:=sixth_physical_parameter_quadrant β hR hI
  have hvr : v.re=c*w.re := by simp [v,Complex.mul_re]
  have hvi : v.im=c*w.im := by simp [v,Complex.mul_im]
  have hvx : 0<v.re := by rw [hvr]; positivity
  have hvy : 0<v.im := by rw [hvi]; positivity
  obtain ⟨hloc,hA,hB,hC,hW⟩:=sixth_octic_selected_bounds β w hR hx hy hX hgraph
  have hvX : 52/85<v.re^2 := by rw [hvr,mul_pow,hc2]; linarith
  have hactualv : (derivative^[10] ((X^3-X-C γ)^6 : Polynomial ℂ)).eval v=0 :=
    (sixth_actual_rows_to_physical β w 10).mp hactual
  have hgv : γ/v=(((91-3*Real.sqrt 429)/10:ℝ):ℂ)*v^2-
      ((208/55-54*Real.sqrt 429/605:ℝ):ℂ)+E/v := by
    calc
      _=16*(β/w) := by rw [hγ]; dsimp [v]; push_cast; field_simp <;> ring
      _=_ := by
        rw [hgraph]
        dsimp [v,E]
        push_cast
        rw [mul_pow,hcc2]
        field_simp <;> ring
  have hEr : E.re/v.re=16*((sixthOcticRemainder w).re/w.re) := by
    dsimp [E,v]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    field_simp <;> ring
  have hEi : E.im/v.im=16*((sixthOcticRemainder w).im/w.im) := by
    dsimp [E,v]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    field_simp <;> ring
  have hAp:=(sixth_octic_remainder_bounds w hx hy hX).1
  have hvW : 52/85≤v.re^2-3*v.im^2 := by
    rw [hvr,hvi,mul_pow,mul_pow,hc2]
    linarith
  change 0≤γ.re ∧ _
  refine ⟨hγR,hγI,hvx,hvy,hvX,hactualv,hgv,?_,?_,?_,?_,?_,hvW⟩
  · rw [hEr]; positivity
  · rw [hEr]; linarith
  · rw [hEi]; linarith
  · rw [hEr,hEi]; linarith
  · rw [hEr,hEi]; linarith
