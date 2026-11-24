-- Prove2me | solution 1 for GaussianPerimeter.tendsto_capScale_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:43:51.91122+00:00
-- url     : https://prove2.me/submissions/f7460852-9ffa-480d-8aac-19bd837f04fd

module
public import Definitions.Def_GaussianPerimeter_LimitBound
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_GaussianPerimeter_NazarovLimit

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    Tendsto (capScale a) atTop (𝓝 0) := by
  have hRho : Tendsto (capRho a) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
      |>.const_mul_atTop ha
  have hSq := (tendsto_pow_atTop (Nat.succ_ne_zero 1)).comp hRho
  have hNeg : Tendsto (fun n => -(capRho a n ^ 2) / 2) atTop atBot := by
    convert hSq.const_mul_atTop_of_neg (show (-1 / 2 : ℝ) < 0 by norm_num) using 1
    ext n
    simp only [Function.comp_apply]
    ring
  have hExp := Real.tendsto_exp_atBot.comp hNeg
  have hDen := hRho.const_mul_atTop (Real.sqrt_pos.2 (by positivity : 0 < 2 * Real.pi))
  change Tendsto (fun n => capScale a n) atTop (𝓝 0)
  simpa only [capScale, Function.comp_def, zero_mul] using
    (hExp.div_atTop hDen).mul_const (Real.exp (a ^ 4 / 4))
end GaussianPerimeter
