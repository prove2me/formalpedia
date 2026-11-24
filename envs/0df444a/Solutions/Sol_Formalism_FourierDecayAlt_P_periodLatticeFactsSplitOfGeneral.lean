-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.periodLatticeFactsSplitOfGeneral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:52.864531+00:00
-- url     : https://prove2.me/submissions/e42c40eb-85de-474e-a0e1-ca9d9b899c36

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x1
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.TextFromGeneral := by
  intro h E _ _ _ hU g₁ g₂ h₁ h₂ ν s _
  exact h E hU _ ν s (Nat.mul_pos h₁.1.pos h₂.1.pos)
end Formalism.FourierDecayAlt.P
