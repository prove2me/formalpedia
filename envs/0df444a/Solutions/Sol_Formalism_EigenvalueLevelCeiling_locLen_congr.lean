-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.locLen_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:20.75712+00:00
-- url     : https://prove2.me/submissions/d3f63ab4-6ba4-40b1-b667-19708cd18fef

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementLoc
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {A A' C C' : Submodule R W} (hA : localization₂ p A = localization₂ p A') (hC : localization₂ p C = localization₂ p C') :
    locLen p A C = locLen p A' C' := by
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [hA, hC]
end Formalism.EigenvalueLevelCeiling
