-- Prove2me | solution 1 for GaussianPerimeter.capScale_mul_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:54.891788+00:00
-- url     : https://prove2.me/submissions/d54d4902-8118-4a74-999b-214dec7a873a

module
public import Definitions.Def_GaussianPerimeter_LimitBound
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_GaussianPerimeter_NazarovLimit
public import Theorems.Thm_GaussianPerimeter_capRho_pos


set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    Real.exp (-(capRho a n ^ 2) / 2) / Real.sqrt (2 * Real.pi) =
      capScale a n * capRho a n * Real.exp (-a ^ 4 / 4) := by
  have hRho := capRho_pos ha hn
  have hπ : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hExp : Real.exp (a ^ 4 / 4) * Real.exp (-a ^ 4 / 4) = 1 := by
    rw [← Real.exp_add, show a ^ 4 / 4 + -a ^ 4 / 4 = 0 by ring, Real.exp_zero]
  rw [capScale]
  calc
    _ = (Real.exp (-(capRho a n ^ 2) / 2) / Real.sqrt (2 * Real.pi)) *
        (Real.exp (a ^ 4 / 4) * Real.exp (-a ^ 4 / 4)) := by rw [hExp, mul_one]
    _ = _ := by field_simp
end GaussianPerimeter
