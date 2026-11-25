-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.leafMackey_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:57:02.592125+00:00
-- url     : https://prove2.me/submissions/e01965b9-bc8c-474e-a315-0f96556ad39c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_isMackey_pi_upper_unipotent_prod_character


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
theorem _root_.solution (O : OnObj S (∀ v, Pm v) c) (χ : ∀ v, AddChar (kf v) (𝓞 K))
    (hG : IsLevelGroups kf n Pm Uv) (hχ : IsGenericChar kf χ) (hU : TieU O Uv) (hψ : TiePsi O χ) : LeafMackey O := by
  unfold LeafMackey
  rw [hU, hψ]
  exact isMackey_pi_upper_unipotent_prod_character K ι kf n χ hχ Pm Uv hG.1 hG.2
end Formalism.L2.Indef.Tree
