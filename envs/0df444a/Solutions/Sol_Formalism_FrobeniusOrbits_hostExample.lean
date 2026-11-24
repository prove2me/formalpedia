-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostExample
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:14.47086+00:00
-- url     : https://prove2.me/submissions/68ebdbb8-78ae-433b-904d-a0ea37a1d037

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerExists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Group
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostExample :=
  ⟨by norm_num [HostHyp], fun e => layerExists (e + 2) 11 7⟩
end Formalism.FrobeniusOrbits
