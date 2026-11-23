-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.product_of_jets
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:45.476725+00:00
-- url     : https://prove2.me/submissions/486e1475-394d-4468-a91a-2776473c7da4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BlockOperatorNormBound
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_jet_exponential_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open MeasureTheory Finset
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : JetsProductBound := by
  intro ι _ n g₀ Th S2 hg hS2 h
  set e : ι → ℝ := fun τ => if n τ = 0 then (1 : ℝ) else min 1 ((g₀ : ℝ) / n τ) with he
  have hg0 : (0 : ℝ) < g₀ := by exact_mod_cast hg
  have hepos : ∀ τ, 0 < e τ := by
    intro τ
    simp only [he]
    split_ifs with h0
    · exact one_pos
    · have : (0 : ℝ) < n τ := by exact_mod_cast Nat.pos_of_ne_zero h0
      exact lt_min one_pos (div_pos hg0 this)
  have hP : 0 < ∏ τ, (1 + e τ) ^ (n τ + g₀) :=
    Finset.prod_pos (fun τ _ => pow_pos (by linarith [hepos τ]) _)
  have h' : Th * (∏ τ, (1 + e τ) ^ (n τ + g₀))⁻¹ ≤ S2 * ∏ τ, ((e τ) ^ g₀)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact h
  have h1 : Th ≤ S2 * (∏ τ, ((e τ) ^ g₀)⁻¹) * ∏ τ, (1 + e τ) ^ (n τ + g₀) := by
    rwa [← div_eq_mul_inv, div_le_iff₀ hP] at h'
  refine h1.trans ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hS2
  refine Finset.prod_le_prod (fun τ _ => ?_) (fun τ _ => ?_)
  · have := hepos τ
    positivity
  · exact Formalism.LogVandermondeBounds.flipTwoThree.jet_exponential_bound (n τ) g₀ hg
end Formalism.HermitianLattices.TraceIntegrality
