-- Prove2me | solution 1 for Formalism.measurable_Gz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:10.871798+00:00
-- url     : https://prove2.me/submissions/ba364cf8-69e4-485c-b241-d909cbee5489

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Theorems.Thm_Formalism_Sz_eq_Sa
import Theorems.Thm_Formalism_vM_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution (h3 : MellinSgen) : Measurable Gz := by
  have := (h3 _ 1 vM_bound).1
  unfold Gz
  rw [Sz_eq_Sa]
  fun_prop
end Formalism
