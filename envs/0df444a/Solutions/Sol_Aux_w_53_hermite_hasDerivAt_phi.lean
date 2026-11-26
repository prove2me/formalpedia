-- Prove2me | solution 1 for Aux_w_53_hermite.hasDerivAt_phi
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:21.869122+00:00
-- url     : https://prove2.me/submissions/792673db-285f-4605-8781-422be4ad2931

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
theorem solution (x : ℝ) : HasDerivAt Aux_w_53_hermite.phi (-x * Aux_w_53_hermite.phi x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
    have hpow := ((hasDerivAt_pow 2 x).div_const (2 : ℝ)).neg
    have hval : -(((2 : ℕ) : ℝ) * x ^ (2 - 1) / 2) = -x := by norm_num
    rw [hval] at hpow
    exact hpow
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have hfn : (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2))) = Aux_w_53_hermite.phi :=
    funext fun y => (Aux_w_53_hermite.phi_def y).symm
  rw [hfn] at h2
  refine h2.congr_deriv ?_
  rw [Aux_w_53_hermite.phi_def]; ring
