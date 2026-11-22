-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.pGroupGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:43.612608+00:00
-- url     : https://prove2.me/submissions/8d3e0220-9084-4e6c-be50-2095c1a87bd9

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : PGroupGen := by
  intro p _ H _ _ hP S hS
  by_contra hne
  obtain ⟨Mx, hMx, hle⟩ := (eq_top_or_exists_le_coatom (Subgroup.closure S)).resolve_left hne
  have := hP.isNilpotent
  have hMn : Mx.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom Mx (Group.normalizerCondition_of_isNilpotent) hMx
  have : Subgroup.normalClosure S ≤ Mx :=
    Subgroup.normalClosure_le_normal (fun x hx => hle (Subgroup.subset_closure hx))
  rw [hS] at this
  exact hMx.1 (top_le_iff.mp this)
end Formalism.TwoAdicCyclotomicDecomposition
