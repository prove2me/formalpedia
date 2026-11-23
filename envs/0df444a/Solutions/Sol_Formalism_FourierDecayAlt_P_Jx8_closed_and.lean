-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.closed_and
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:55.667104+00:00
-- url     : https://prove2.me/submissions/59d29ddf-ef82-4db1-a074-365064e23d3b

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution {X : Type} [TopologicalSpace X] {p q : X → Prop} (hp : IsClosed {x | p x})
    (hq : IsClosed {x | q x}) : IsClosed {x | p x ∧ q x} := hp.inter hq
end Formalism.FourierDecayAlt.P.Jx8
