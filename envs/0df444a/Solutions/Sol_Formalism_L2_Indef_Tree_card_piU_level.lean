-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.card_piU_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:38:50.909554+00:00
-- url     : https://prove2.me/submissions/57ce9c4b-4f41-43aa-b0d1-55609acaee04

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Theorems.Thm_Formalism_L2_Indef_Tree_card_piU_eq

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
theorem _root_.solution (hG : IsLevelGroups kf n Pm Uv) (g1 g2 fN : ℕ) (h12 : g1 ≠ g2)
    (hor : ∀ v, Fintype.card (kf v) = g1 ∨ Fintype.card (kf v) = g2)
    (hc1 : (Finset.univ.filter fun v => Fintype.card (kf v) = g1).card = fN)
    (hc2 : (Finset.univ.filter fun v => Fintype.card (kf v) = g2).card = fN) :
    Nat.card (Subgroup.pi Set.univ Uv) = g1 ^ ((n + 1) * n / 2 * fN) * g2 ^ ((n + 1) * n / 2 * fN) := by
  classical
  rw [card_piU_eq hG, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => Fintype.card (kf v) = g1)]
  have hfilt : (Finset.univ.filter fun v => ¬ Fintype.card (kf v) = g1) =
      (Finset.univ.filter fun v => Fintype.card (kf v) = g2) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact (hor v).resolve_left h
    · intro h h'; exact h12 (h'.symm.trans h)
  rw [hfilt]
  have e1 : ∏ v ∈ Finset.univ.filter (fun v => Fintype.card (kf v) = g1), Fintype.card (kf v) ^ ((n + 1) * n / 2) =
      ∏ _v ∈ Finset.univ.filter (fun v => Fintype.card (kf v) = g1), g1 ^ ((n + 1) * n / 2) :=
    Finset.prod_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2]
  have e2 : ∏ v ∈ Finset.univ.filter (fun v => Fintype.card (kf v) = g2), Fintype.card (kf v) ^ ((n + 1) * n / 2) =
      ∏ _v ∈ Finset.univ.filter (fun v => Fintype.card (kf v) = g2), g2 ^ ((n + 1) * n / 2) :=
    Finset.prod_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2]
  rw [e1, e2, Finset.prod_const, Finset.prod_const, hc1, hc2, ← pow_mul, ← pow_mul]
end Formalism.L2.Indef.Tree
