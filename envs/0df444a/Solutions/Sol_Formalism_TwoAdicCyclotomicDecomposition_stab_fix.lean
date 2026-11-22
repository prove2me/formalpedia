-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.stab_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:13:04.566454+00:00
-- url     : https://prove2.me/submissions/251035b8-b31a-406b-b855-a9d978a1e89d

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Theorems.Thm_Bl_FirstBlockLemmaE_goal1
import Theorems.Thm_Bl_general_b_fact_right_ter_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ)
    (hx : x ^ 2 = ((4 * (2 * c) + 1 : ℤ) : L))
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] (σ : Gal(L/ℚ))
    (hσ : σ ∈ MulAction.stabilizer Gal(L/ℚ) P) : σ x = x := by
  exact Bl.general_b_fact_right_ter_form.goal1 x c hx P σ hσ
end Formalism.TwoAdicCyclotomicDecomposition
