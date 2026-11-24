-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostReal_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:56:11.374096+00:00
-- url     : https://prove2.me/submissions/dec0919b-769f-47d5-ad57-bd24ee51b4b6

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_JumpSets
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Theorems.Thm_UpperTheory_Reformulated_B_JumpSetsAlt_hostReal_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open ConjReal
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (hGal : HostGalois) (hSpec : HostGalSpec) (hConj : HostConj) : HostReal :=
  _root_.UpperTheory.Reformulated.B.JumpSetsAlt.hostReal_of hGal hSpec hConj
end Formalism.FrobeniusOrbits
