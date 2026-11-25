-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.card_piU_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:22:40.479879+00:00
-- url     : https://prove2.me/submissions/22935409-3f06-4775-a9bc-d859ed2f7687

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Theorems.Thm_Formalism_L2_Indef_Tree_card_Uv
import Theorems.Thm_Formalism_L2_Indef_Tree_card_piU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain CategoryTheory
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type} [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}
variable {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} {Uv : ∀ v, Subgroup (Pm v)}
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (hG : IsLevelGroups kf n Pm Uv) :
    Nat.card (Subgroup.pi Set.univ Uv) = ∏ v, Fintype.card (kf v) ^ ((n + 1) * n / 2) := by
  rw [card_piU]
  exact Finset.prod_congr rfl fun v _ => card_Uv hG v
end Formalism.L2.Indef.Tree
