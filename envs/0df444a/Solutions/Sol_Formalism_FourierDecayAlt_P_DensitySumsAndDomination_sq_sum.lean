-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DensitySumsAndDomination.sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:45.306846+00:00
-- url     : https://prove2.me/submissions/c4ef4a2c-2c0d-4718-b72b-0d6c4cfe21fd

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DensitySumsAndDomination
namespace Formalism.FourierDecayAlt.P.DensitySumsAndDomination
theorem _root_.solution (M : ℕ) : ∑ m ∈ Icc 2 (M + 2), (((m : ℕ) : ℝ) ^ 2)⁻¹ ≤ 3 / 4 - ((M : ℝ) + 2)⁻¹ := by
  induction M with
  | zero => norm_num [Finset.Icc_self]
  | succ M ih =>
    have hs : ∑ m ∈ Icc 2 (M + 1 + 2), (((m : ℕ) : ℝ) ^ 2)⁻¹
        = ∑ m ∈ Icc 2 (M + 2), (((m : ℕ) : ℝ) ^ 2)⁻¹ + (((M : ℝ) + 3) ^ 2)⁻¹ := by
      rw [show M + 1 + 2 = (M + 2) + 1 by omega, Finset.sum_Icc_succ_top (by omega)]
      first
        | (push_cast; ring)
        | (congr 1; push_cast; ring)
    have hc2 : ((M + 1 : ℕ) : ℝ) + 2 = (M : ℝ) + 3 := by push_cast; ring
    rw [hs, hc2]
    have h2 : (0 : ℝ) < (M : ℝ) + 2 := by positivity
    have h3 : (0 : ℝ) < (M : ℝ) + 3 := by positivity
    have h2' := h2.ne'
    have h3' := h3.ne'
    have e : ((M : ℝ) + 2)⁻¹ - ((M : ℝ) + 3)⁻¹ - (((M : ℝ) + 3) ^ 2)⁻¹
        = (((M : ℝ) + 2) * ((M : ℝ) + 3) ^ 2)⁻¹ := by
      field_simp
      ring
    have hpos : 0 ≤ (((M : ℝ) + 2) * ((M : ℝ) + 3) ^ 2)⁻¹ := by positivity
    linarith
end Formalism.FourierDecayAlt.P.DensitySumsAndDomination
