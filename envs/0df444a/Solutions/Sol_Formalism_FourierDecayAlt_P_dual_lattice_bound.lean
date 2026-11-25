-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dual_lattice_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:39:41.678688+00:00
-- url     : https://prove2.me/submissions/61b86736-cb05-4aa8-9610-8a326616cd5b

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : DualLattice := by
  intro E A _ _ ψ O La g hg
  have key : ∀ x y : E, g ^ 2 * x * y / g = x * (g * y) := by
    intro x y; field_simp
  refine ⟨?_, ?_⟩
  · ext y; simp only [Set.mem_setOf_eq, key]
  · intro hO y hy x hx
    have := hy (g ^ 2 * x) (hO x hx)
    rwa [key] at this
end Formalism.FourierDecayAlt.P
