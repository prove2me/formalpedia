-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostDiscr_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:57:13.293525+00:00
-- url     : https://prove2.me/submissions/7289ea22-7855-4e0e-a014-b999b9840dbe

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_discr_hostE
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_discr_hostF
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_rdE
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_rdF
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_sqF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (h1 : DiscrMaximalRealCyclotomic) : HostDiscr := by
  intro e q d hH L _ _ ζ a b h
  have hq : 0 < q := hH.1.pos
  have hd : 0 < d := hH.2.1.pos
  have hE := DiscrB.discr_hostE h1 hH h
  have hF := DiscrB.discr_hostF h1 hH h
  refine ⟨hE, hF, by rw [hE, hF]; exact (DiscrB.sqF e q d).symm, ?_, ?_⟩
  · rw [hE]; exact DiscrB.rdE e q d hq hd
  · rw [hF]; exact DiscrB.rdF e q d hq hd
end Formalism.FrobeniusOrbits
