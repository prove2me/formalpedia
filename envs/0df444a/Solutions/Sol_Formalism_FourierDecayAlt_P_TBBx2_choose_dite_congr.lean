-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.choose_dite_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:31.940806+00:00
-- url     : https://prove2.me/submissions/0643c4e7-5619-438a-bc83-b19e42dd05c2

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.TBBx2
theorem _root_.solution {α E : Type*} [Zero E] (P Q : α → Prop) (hPQ : P = Q) (f g : α → E)
    [Decidable (∃ θ, P θ)] [Decidable (∃ θ, Q θ)]
    (hfg : ∀ θ, P θ → f θ = g θ) :
    (if h : ∃ θ, P θ then f h.choose else 0) = (if h : ∃ θ, Q θ then g h.choose else 0) := by
  subst hPQ
  split_ifs with h1 <;> first | rfl | exact hfg _ h1.choose_spec
end Formalism.FourierDecayAlt.P.TBBx2
