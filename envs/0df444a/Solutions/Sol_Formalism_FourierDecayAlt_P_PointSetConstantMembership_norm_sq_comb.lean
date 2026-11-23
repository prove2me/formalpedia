-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PointSetConstantMembership.norm_sq_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:43.92887+00:00
-- url     : https://prove2.me/submissions/1a7b49f9-eaef-4ee1-80b4-38b9c6381a34

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointSetConstantMembership

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PointSetConstantMembership
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P.PointSetConstantMembership
theorem _root_.solution {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : Finset α) (c : α → ℂ) (V : α → H) :
    ((‖∑ p ∈ P, c p • V p‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ P, ∑ p' ∈ P, (conj (c p) * c p') * ⟪V p, V p'⟫_ℂ := by
  have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ p ∈ P, c p • V p)
  rw [Complex.ofReal_pow]
  refine this.symm.trans ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring
end Formalism.FourierDecayAlt.P.PointSetConstantMembership
