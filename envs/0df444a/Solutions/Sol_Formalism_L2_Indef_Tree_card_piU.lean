-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.card_piU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:53.879116+00:00
-- url     : https://prove2.me/submissions/a33c45ea-af99-47a5-91da-58b642fb4b2d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves

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
theorem _root_.solution : Nat.card (Subgroup.pi Set.univ Uv) = ∏ v, Nat.card (Uv v) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x v => ⟨x.1 v, (Subgroup.mem_pi _).mp x.2 v (Set.mem_univ v)⟩
      invFun := fun y => ⟨fun v => (y v).1, (Subgroup.mem_pi _).mpr fun v _ => (y v).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end Formalism.L2.Indef.Tree
