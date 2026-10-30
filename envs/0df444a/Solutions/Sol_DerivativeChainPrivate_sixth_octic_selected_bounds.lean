-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_selected_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:03:20.571338+00:00
-- url     : https://prove2.me/submissions/2d04ac7e-58f9-4899-876e-0a052f006ee3

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_remainder_bounds
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_weighted_corrections
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
namespace DerivativeChainPrivate

theorem sixth_octic_scalar_gaps :
    (1/50:ℝ)<(91-3*Real.sqrt 429)/1360 ∧ (91-3*Real.sqrt 429)/1360<11/500 ∧
    (91-3*Real.sqrt 429)/1360<(455-3*Real.sqrt 15145)/2720 ∧
    (3/100:ℝ)<(13/32-77*Real.sqrt 15145/37280)-(13/55-27*Real.sqrt 429/4840) ∧
    (11/100:ℝ)<(91+3*Real.sqrt 429)/1360 ∧
    13/55+27*Real.sqrt 429/4840<9/25 ∧
    (3/20:ℝ)<13/32-77*Real.sqrt 15145/37280 ∧
    (3/250:ℝ)<(13/55-27*Real.sqrt 429/4840)-(51/10)*((91-3*Real.sqrt 429)/1360) ∧
    (9/1000:ℝ)<(13/55-27*Real.sqrt 429/4840)-(26/5)*((91-3*Real.sqrt 429)/1360) ∧
    (455-3*Real.sqrt 15145)/2720<4/125 := by
  have h1:=Real.sq_sqrt (by norm_num : (0:ℝ)≤429)
  have p1:=Real.sqrt_nonneg 429
  have h2:=Real.sq_sqrt (by norm_num : (0:ℝ)≤15145)
  have p2:=Real.sqrt_nonneg 15145
  have l1 : (2071231517:ℝ)/100000000<Real.sqrt 429 := by nlinarith only [h1,p1]
  have u1 : Real.sqrt 429<(2071231518:ℝ)/100000000 := by nlinarith only [h1,p1]
  have l2 : (1230650:ℝ)/10000<Real.sqrt 15145 := by nlinarith only [h2,p2]
  have u2 : Real.sqrt 15145<(1230651:ℝ)/10000 := by nlinarith only [h2,p2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [l1,u1,l2,u2]
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DerivativeChainPrivate
open scoped BigOperators



theorem sixth_octic_A_at_four (z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : 4≤z.re^2) :
    (sixthOcticRemainder z).re/z.re≤3/250 := by
  apply (sixth_octic_weighted_corrections 4 le_rfl z hx hy hX).1.trans
  norm_num [sixthOcticExpansionBounds,Fin.sum_univ_succ]

theorem sixth_octic_A_at_fiftyone (z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : 51/10≤z.re^2) :
    (sixthOcticRemainder z).re/z.re≤9/1000 := by
  apply (sixth_octic_weighted_corrections (51/10) (by norm_num) z hx hy hX).1.trans
  norm_num [sixthOcticExpansionBounds,Fin.sum_univ_succ]

theorem sixth_octic_C_at_twentysix (z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : 26/5≤z.re^2) :
    (3*((sixthOcticRemainder z).re/z.re)-(sixthOcticRemainder z).im/z.im)/2≤73/4000 := by
  apply (sixth_octic_weighted_corrections (26/5) (by norm_num) z hx hy hX).2.trans
  norm_num [sixthOcticExpansionBounds,Fin.sum_univ_succ]
end DerivativeChainPrivate

theorem solution (β z : ℂ) (hR : 0≤β.re) (hx : 0<z.re) (hy : 0<z.im)
    (hX : 4≤z.re^2)
    (hg : β/z=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
      ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z) :
    26/5<z.re^2 ∧ (sixthOcticRemainder z).re/z.re≤9/1000 ∧
      (sixthOcticRemainder z).im/z.im≤0 ∧
      (3*((sixthOcticRemainder z).re/z.re)-(sixthOcticRemainder z).im/z.im)/2≤73/4000 ∧
      26/5≤z.re^2-3*z.im^2 := by
  let α:=(91-3*Real.sqrt 429)/1360
  let b:=13/55-27*Real.sqrt 429/4840
  obtain ⟨ha,_,_,_,_,_,_,hs₁,hs₂,_⟩:=sixth_octic_scalar_gaps
  change (1/50:ℝ)<α at ha
  change (3/250:ℝ)<b-(51/10)*α at hs₁
  change (9/1000:ℝ)<b-(26/5)*α at hs₂
  have hz : z≠0 := by intro he; simp [he] at hx
  have hr:=(cubic_graph_coordinate_parts β z (sixthOcticRemainder z) α b hz hg).1
  have hRp : β.re/z.re=α*(z.re^2-3*z.im^2)-b+(sixthOcticRemainder z).re/z.re := by rw [hr]; field_simp
  have hn : 0≤β.re/z.re := div_nonneg hR hx.le
  have ht:=mul_nonneg (show 0≤α by linarith) (sq_nonneg z.im)
  have hA₁:=sixth_octic_A_at_four z hx hy hX
  have hX₁ : 51/10<z.re^2 := by
    have hh : α*(51/10)<α*z.re^2 := by nlinarith only [hRp,hn,ht,hA₁,hs₁]
    exact lt_of_mul_lt_mul_left hh (by linarith only [ha])
  have hA₂:=sixth_octic_A_at_fiftyone z hx hy hX₁.le
  have hX₂ : 26/5<z.re^2 := by
    have hh : α*(26/5)<α*z.re^2 := by nlinarith only [hRp,hn,ht,hA₂,hs₂]
    exact lt_of_mul_lt_mul_left hh (by linarith only [ha])
  have hC:=sixth_octic_C_at_twentysix z hx hy hX₂.le
  have hB:=(sixth_octic_remainder_bounds z hx hy hX).2.2.2
  refine ⟨hX₂,hA₂,hB.le,hC,?_⟩
  have hh : α*(26/5)<α*(z.re^2-3*z.im^2) := by linarith only [hRp,hn,hA₂,hs₂]
  exact (lt_of_mul_lt_mul_left hh (by linarith only [ha])).le
