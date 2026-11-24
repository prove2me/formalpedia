-- Prove2me | solution 1 for Formalism.HF.hostDensity_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:13:45.719892+00:00
-- url     : https://prove2.me/submissions/d5096c31-2c2c-4ec0-b223-15fffb7227a9

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
import Theorems.Thm_Formalism_HF_P_dirDensity_congr
import Theorems.Thm_Formalism_HF_P_frob_iff_chi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Filter Topology Formalism.Q3
noncomputable section
open Formalism Formalism.HF
namespace Formalism.HF
theorem _root_.solution (hA : HostDensityArith) : HostDensity := by
  intro q hq E _ _ α hE g
  refine P.dirDensity_congr (hA q hq g).2 ?_
  intro p hp
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hpq, hchi⟩
    exact ⟨hpq, (P.frob_iff_chi q hq E α hE g p hp hpq).2 hchi⟩
  · rintro ⟨hpq, hfrob⟩
    exact ⟨hpq, (P.frob_iff_chi q hq E α hE g p hp hpq).1 hfrob⟩
end Formalism.HF
