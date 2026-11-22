-- Prove2me | solution 1 for Formalism.HF.hostDiscr_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:56.699221+00:00
-- url     : https://prove2.me/submissions/05220e78-b72c-4579-a9cc-1d755ea0ebeb

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace Formalism.Q3
noncomputable section
open Formalism Formalism.HF
namespace Formalism.HF
theorem _root_.solution (h : MQDiscr) : HostDiscr := by
  intro q hq E _ _ α hα
  unfold Formalism.Q3.Hyp3 at hq
  obtain ⟨hq1, hinj⟩ := hq
  rw [h 3 q (by norm_num) hq1 hinj E α hα, Fin.prod_univ_three]
  push_cast
  ring
end Formalism.HF
