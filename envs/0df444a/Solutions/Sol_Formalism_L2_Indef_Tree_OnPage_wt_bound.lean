-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.wt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:48:56.205045+00:00
-- url     : https://prove2.me/submissions/f6cc09c7-fef4-4c37-bc01-9ed6aab94c29

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
namespace Formalism.L2.Indef.Tree.OnPage
theorem _root_.solution (O : OnObj S P c) (hW : LeafW O) (j : Bs.J) : 0 ≤ O.wt j ∧ O.wt j ≤ 2 * O.f * O.b := by
  obtain ⟨nf, hnf, hw⟩ := hW
  obtain ⟨ws, hs, hb⟩ := hw j
  rw [hs]
  refine ⟨Finset.sum_nonneg (fun τ _ => (hb τ).1), ?_⟩
  calc ∑ τ, ws τ ≤ ∑ _τ : Fin nf, 2 * O.b := Finset.sum_le_sum (fun τ _ => (hb τ).2)
    _ = 2 * O.f * O.b := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hnf]; ring
end Formalism.L2.Indef.Tree.OnPage
