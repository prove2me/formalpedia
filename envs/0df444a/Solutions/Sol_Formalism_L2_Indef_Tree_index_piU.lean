-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.index_piU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:44.323895+00:00
-- url     : https://prove2.me/submissions/bde2c69e-faf3-465c-badb-c5aef7988a08

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Theorems.Thm_Formalism_L2_Indef_Tree_card_Pm
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
    (Subgroup.pi Set.univ Uv).index = ∏ v, ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card (kf v) ^ i - 1) := by
  have h1 := Subgroup.card_mul_index (Subgroup.pi Set.univ Uv)
  rw [Nat.card_pi] at h1
  simp only [card_Pm hG] at h1
  rw [Finset.prod_mul_distrib, ← card_piU] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
end Formalism.L2.Indef.Tree
