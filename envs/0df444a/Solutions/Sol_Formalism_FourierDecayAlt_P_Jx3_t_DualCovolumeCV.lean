-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.t_DualCovolumeCV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:24.16369+00:00
-- url     : https://prove2.me/submissions/42567547-35b2-41f9-ad4b-f9ddbeab0fd0

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution : DualCovolumeCV := by
  intro hL hE hB E _ _ _ hDL hCD hU g ν s hg
  obtain ⟨a, b, c⟩ := hB hL hE E hU g ν s hg
  have := a
  have : IsZLattice ℝ (eLat E (S6.perLat E g ν s) (S6.rd E ^ (-ν))) := ⟨b⟩
  obtain ⟨d1, d2⟩ := hDL (eLat E (S6.perLat E g ν s) (S6.rd E ^ (-ν)))
  have := d1
  have := d2
  rw [hCD (eLat E (S6.perLat E g ν s) (S6.rd E ^ (-ν))), c]
end Formalism.FourierDecayAlt.P.Jx3
