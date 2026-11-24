-- Prove2me | solution 1 for Formalism.CohomologicalDescent.exact_exponent_lattice_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:39:07.450274+00:00
-- url     : https://prove2.me/submissions/675bf625-5dd8-4900-a425-c7318ad589da

import Definitions.Def_Formalism_PieriBlockIdeals_JointTheoremALoc
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent
open TensorProduct Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization
namespace Formalism.CohomologicalDescent
theorem _root_.solution {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) (h : ∃ e, LatIncl l B e) : LatIncl l B (exactExp l B) :=
  Nat.sInf_mem (s := {e : ℕ | LatIncl l B e}) h
end Formalism.CohomologicalDescent
