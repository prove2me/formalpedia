-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.card_Uv_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:52:24.086702+00:00
-- url     : https://prove2.me/submissions/76697198-3fbe-40bb-a699-5d4463413309

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_isMirab_of_isUniU


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
theorem _root_.solution (hG : IsLevelGroups kf n Pm Uv) (v : ι) :
    Nat.card (Uv v) =
      Nat.card {u : GL (Fin (n + 1)) (kf v) // PI.MirabIndex.IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (kf v))} :=
  Nat.card_congr
    { toFun := fun h => ⟨((h : Pm v) : GL (Fin (n + 1)) (kf v)), (hG.2 v h).1 h.2⟩
      invFun := fun u => ⟨⟨u.1, (hG.1 v u.1).2 (isMirab_of_isUniU _ u.2)⟩, (hG.2 v _).2 u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end Formalism.L2.Indef.Tree
