-- Prove2me | solution 1 for Formalism.BasicNotions.hypOdd_of_hostHyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:20:00.93581+00:00
-- url     : https://prove2.me/submissions/1207c9ed-7400-47a4-91c3-37b7ce8950c1

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_LocalRingCardinality_DataHost

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
open Formalism Formalism.BasicNotions
namespace Formalism.BasicNotions
theorem _root_.solution {q d : ℕ} (h : HostHyp q d) : HypOdd q d := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := h
  refine ⟨hq, hd, ?_, ?_, ?_⟩ <;> rintro rfl <;> omega
end Formalism.BasicNotions
