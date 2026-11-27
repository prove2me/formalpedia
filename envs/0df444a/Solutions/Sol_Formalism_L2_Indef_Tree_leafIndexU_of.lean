-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.leafIndexU_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:18.421703+00:00
-- url     : https://prove2.me/submissions/6859bbd1-f6a2-423c-b034-b32e0fbbeeda

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Theorems.Thm_Formalism_L2_Indef_Tree_index_piU
import Theorems.Thm_Formalism_L2_Indef_Tree_card_piU_eq
import Theorems.Thm_Formalism_L2_Indef_Tree_sum_inv_le_y
import Theorems.Thm_product_lowerBound


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
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type} [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}
variable {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} {Uv : ∀ v, Subgroup (Pm v)}
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (O : OnObj S (∀ v, Pm v) c) (fN : ℕ) (hG : IsLevelGroups kf n Pm Uv)
    (hSq : LeafLevelSq O kf fN) (hY : LeafYBound O) (hU : TieU O Uv) (hN : TieLevelNum O n fN) : LeafIndexU O := by
  unfold LeafIndexU
  rw [hU, index_piU hG, card_piU_eq hG]
  have hsum := sum_inv_le_y O fN hSq hN.1 hY
  have hB := product_lowerBound ι Finset.univ (fun v => Fintype.card (kf v)) (n + 1) O.y
    (fun v _ => Fintype.one_lt_card) hsum
  simp only [Nat.add_sub_cancel] at hB
  have hcast : ((∏ v, ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card (kf v) ^ i - 1) : ℕ) : ℝ) =
      ∏ v, ∏ i ∈ Finset.Ico 1 (n + 1), ((Fintype.card (kf v) : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos)]
    push_cast
    ring
  rw [hcast]
  push_cast
  exact hB
end Formalism.L2.Indef.Tree
