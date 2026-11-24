-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.initSeg_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:48:30.506918+00:00
-- url     : https://prove2.me/submissions/0dc76fdf-89b0-46a8-8962-53bc7a83c46d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_card_initSeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution {h k : ℕ} (hh : h ≤ n) (hk : (initSeg n h).card = k) (i : Fin k) :
    ((initSeg n h).orderEmbOfFin hk i).val = i.val := by
  have hkh : k = h := by rw [← hk, card_initSeg hh]
  have hlt : ∀ j : Fin k, j.val < n := fun j => by have := j.2; omega
  have := Finset.orderEmbOfFin_unique hk (f := fun j : Fin k => (⟨j.val, hlt j⟩ : Fin n))
    (fun j => by
      unfold initSeg
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by have := j.2; simp only; omega⟩)
    (fun j j' hjj => hjj)
  rw [← congr_fun this i]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
