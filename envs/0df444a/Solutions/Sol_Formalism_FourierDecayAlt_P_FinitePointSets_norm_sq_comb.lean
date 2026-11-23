-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FinitePointSets.norm_sq_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:12.945354+00:00
-- url     : https://prove2.me/submissions/e241d2e8-c00a-4727-bcdf-4d7b8326c263

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinitePointSets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FinitePointSets
open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P.FinitePointSets
theorem _root_.solution {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (c : α → ℂ) (V : α → H) :
    ((‖∑ p ∈ Y, c p • V p‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ Y, ∑ q ∈ Y, (c p * conj (c q)) * ⟪V q, V p⟫ := by
  have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ p ∈ Y, c p • V p)
  rw [Complex.ofReal_pow]
  refine this.symm.trans ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring
end Formalism.FourierDecayAlt.P.FinitePointSets
