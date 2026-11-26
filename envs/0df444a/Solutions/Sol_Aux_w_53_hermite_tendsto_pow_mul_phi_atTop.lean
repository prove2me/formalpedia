-- Prove2me | solution 1 for Aux_w_53_hermite.tendsto_pow_mul_phi_atTop
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:22.481517+00:00
-- url     : https://prove2.me/submissions/7bd8d18e-49c7-482d-b8c3-4527f25ae05c

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Mathlib
set_option autoImplicit false
namespace Aux_w_53_hermite
end Aux_w_53_hermite
open Aux_w_53_hermite
open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal
theorem solution (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * Aux_w_53_hermite.phi x) atTop (𝓝 0) := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [mul_zero] at ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (pow_nonneg hx k) (Aux_w_53_hermite.phi_pos x).le
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [Aux_w_53_hermite.phi_def]
    have hx0 : 0 ≤ x := by linarith
    have hexp : Real.exp (-(x ^ 2 / 2)) ≤ Real.exp (-x) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hmul : (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) ≤
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    calc x ^ k * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)))
        ≤ x ^ k * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left hmul (pow_nonneg hx0 k)
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * (x ^ k * Real.exp (-x)) := by ring
