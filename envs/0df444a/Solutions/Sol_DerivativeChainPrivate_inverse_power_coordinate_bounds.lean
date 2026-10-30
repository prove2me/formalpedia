-- Prove2me | solution 1 for DerivativeChainPrivate.inverse_power_coordinate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:38:30.532801+00:00
-- url     : https://prove2.me/submissions/d926d724-89ef-451b-b981-533c6f733008

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (q : ℕ) (z : ℂ) (hx : 0<z.re) (hy : 0<z.im) :
    |((z⁻¹)^(q+1)).re/z.re|≤(z.re⁻¹)^(q+2) ∧
      |((z⁻¹)^(q+1)).im/z.im|≤(q+1:ℝ)*(z.re⁻¹)^(q+2) := by
  let x:=z.re
  let f:=fun v : ℂ => (v⁻¹)^(q+1)
  let S:={v : ℂ|x≤v.re}
  have hx' : 0<x := hx
  have hderiv (v : ℂ) (hv : v∈S) :
      HasDerivAt f (((q+1:ℕ):ℂ)*(v⁻¹)^q*(-(v^2)⁻¹)) v := by
    have hv0 : v≠0 := by intro he; simp [S,he] at hv; linarith
    simpa only [f,Function.comp_def,Nat.add_sub_cancel] using
      (hasDerivAt_pow (q+1) (v⁻¹)).comp v (hasDerivAt_inv hv0)
  have hnorm (v : ℂ) (hv : v∈S) : x≤‖v‖ :=
    le_trans hv (Complex.re_le_norm v)
  have hbound (v : ℂ) (hv : v∈S) : ‖deriv f v‖≤(q+1:ℝ)*(x⁻¹)^(q+2) := by
    rw [(hderiv v hv).deriv]
    simp only [norm_mul,norm_neg,norm_inv,norm_pow,Complex.norm_natCast]
    norm_num only [Nat.cast_add,Nat.cast_one]
    have hi : ‖v‖⁻¹≤x⁻¹ := inv_anti₀ hx' (hnorm v hv)
    have hi2 : (‖v‖^2)⁻¹≤(x⁻¹)^2 := by rw [←inv_pow]; gcongr
    calc
      _≤(q+1:ℝ)*(x⁻¹)^q*(x⁻¹)^2 := by gcongr
      _=(q+1:ℝ)*(x⁻¹)^(q+2) := by rw [pow_add]; ring
  have hc : Convex ℝ S := (convex_Ici x).linear_preimage Complex.reLm
  have hzS : z∈S := by simp [S,x]
  have hxS : (x:ℂ)∈S := by simp [S]
  have hdf : ∀ v∈S,DifferentiableAt ℂ f v := fun v hv => (hderiv v hv).differentiableAt
  have hb : ∀ v∈S,‖deriv f v‖≤(q+1:ℝ)*(x⁻¹)^(q+2) := hbound
  have hLip:=Convex.norm_image_sub_le_of_norm_deriv_le hdf hb hc hxS hzS
  have hfx : (f (x:ℂ)).im=0 := by simp [f,←Complex.ofReal_inv,←Complex.ofReal_pow]
  have hImag:=Complex.abs_im_le_norm (f z-f (x:ℂ))
  rw [Complex.sub_im,hfx,sub_zero] at hImag
  have hIm:=hImag.trans hLip
  have he : z-(x:ℂ)=Complex.I*(z.im:ℂ) := by apply Complex.ext <;> simp [x]
  rw [he,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy] at hIm
  have hfn : ‖f z‖≤(x⁻¹)^(q+1) := by
    dsimp [f]
    rw [norm_pow,norm_inv]
    gcongr
    exact hnorm z hzS
  have hRe:=(Complex.abs_re_le_norm (f z)).trans hfn
  constructor
  · rw [abs_div,abs_of_pos hx]
    apply (div_le_iff₀ hx).mpr
    calc
      _≤(x⁻¹)^(q+1) := hRe
      _=(x⁻¹)^(q+2)*x := by
        symm
        rw [show q+2=q+1+1 by omega,pow_succ,mul_assoc,inv_mul_cancel₀ hx'.ne',mul_one]
  · rw [abs_div,abs_of_pos hy]
    apply (div_le_iff₀ hy).mpr
    exact hIm
