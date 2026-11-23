-- Prove2me | solution 1 for Formalism.DimensionVariation.size_at_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:16.625797+00:00
-- url     : https://prove2.me/submissions/2062eb61-781f-4134-a99c-8db1bbd57545

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementC
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution : SizeAtEmbedding := by
  intro Pl _ r g0 ν n Om Ksq kc Msq Th0sq hh hK hkc hM hT hhh hOm h
  have hf : ∀ τ, Real.log ((Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i)))) =
      ((∑ i, ph (ν τ i)) - (n τ : ℝ) * Real.log (Om τ)) +
        (1 + 2 * (g0 : ℝ) * Real.log (2 * (n τ : ℝ) + 2)) := by
    intro τ
    have h2 : (0 : ℝ) < 2 * n τ + 2 := by positivity
    have h3 := hOm τ
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_inv,
      Real.log_exp, Real.log_exp]
    push_cast; ring
  have hpos : ∀ τ, 0 < (Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i))) := by
    intro τ
    have h3 := hOm τ
    positivity
  have hP : 0 < ∏ τ, ((Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i)))) :=
    Finset.prod_pos (fun τ _ => hpos τ)
  refine le_trans (Real.log_le_log hK h) (le_of_eq ?_)
  rw [Real.log_mul hhh.ne' (by positivity), Real.log_mul (by positivity) hP.ne',
    Real.log_prod (fun τ _ => (hpos τ).ne'), Finset.sum_congr rfl (fun τ _ => hf τ),
    Finset.sum_add_distrib, Real.log_mul (by positivity) hT.ne', Real.log_mul (by positivity) hM.ne',
    Real.log_pow]
  push_cast; ring
end Formalism.DimensionVariation
