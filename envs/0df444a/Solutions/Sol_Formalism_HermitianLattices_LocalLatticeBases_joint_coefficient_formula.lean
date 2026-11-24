-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.joint_coefficient_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:05.197259+00:00
-- url     : https://prove2.me/submissions/7111b3a4-6259-4e3d-ac9b-6f1ea09e5694

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : Joint_coef := by
  intro ι TT a W L k m f q e logP muM0 muRam muN EP E0 Eprice hL hk hm hf hq ha hW h1 h2 h3 h4
  have hk0 : 0 < k := by linarith
  have key : ∑ τ ∈ TT, m * (a τ / k + 3 * W τ + k) * (1 + 2 * f / q) ≤
      m / k * (∑ τ ∈ TT, a τ) + ∑ τ ∈ TT, (m * (3 * W τ + k) * (1 + 2 * f / q) + m * f / (2 * k)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro τ hτ
    obtain ⟨h0, h4a⟩ := ha τ hτ
    have : a τ / q ≤ 1 / 4 := by rw [div_le_iff₀ hq]; linarith
    have e1 : m * (a τ / k + 3 * W τ + k) * (1 + 2 * f / q) =
      m / k * a τ + m * (3 * W τ + k) * (1 + 2 * f / q) + (2 * m * f / k) * (a τ / q) := by
      field_simp; ring
    have e2 : m * f / (2 * k) = (2 * m * f / k) * (1/4) := by field_simp; ring
    rw [e1, e2]
    have : (2 * m * f / k) * (a τ / q) ≤ (2 * m * f / k) * (1/4) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have key2 := mul_le_mul_of_nonneg_right key hL.le
  have e3 : -(1 - (m + 1) / k) * (∑ τ ∈ TT, a τ) * L = -(∑ τ ∈ TT, a τ) * L + (∑ τ ∈ TT, a τ) / k * L + m / k * (∑ τ ∈ TT, a τ) * L := by
    field_simp; ring
  rw [e3]
  nlinarith
end Formalism.HermitianLattices.LocalLatticeBases
