-- Prove2me | solution 1 for GaussianPerimeter.gaussianLowerBound_numeric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:36:34.644033+00:00
-- url     : https://prove2.me/submissions/c253f13e-bb20-4255-a463-6127dbe64ab0

module
public import Definitions.Def_GaussianPerimeter_Quadrature
public import Definitions.Def_GaussianPerimeter_Prefactor
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GaussianPerimeter_QuadratureCertificate
public import Theorems.Thm_GaussianPerimeter_lowerBound_integral
public import Theorems.Thm_GaussianPerimeter_gaussianPrefactor_lower


set_option autoImplicit true
@[expose] public section
public section
open Finset
open GaussianPerimeter
local notation "A" => (6131 / 5000)
local notation "B" => (2387 / 1000)
local notation "F" => lowerBoundIntegrand A B
namespace GaussianPerimeter
theorem _root_.solution :
    (0.31258 : ℝ) ≤ (B * A * Real.exp (-A ^ 4 / 4) / Real.sqrt Real.pi) *
      (∫ x in (-6 : ℝ)..6, Real.exp (-x ^ 2 - B * Real.exp (A ^ 2 * x))) := by
  calc
    _ ≤ (0.938393 : ℝ) * (0.333104 : ℝ) := by norm_num
    _ ≤ _ := mul_le_mul gaussianPrefactor_lower lowerBound_integral (by norm_num)
      ((show (0 : ℝ) ≤ 0.938393 by norm_num).trans gaussianPrefactor_lower)
end GaussianPerimeter
