-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.eDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:21:09.572868+00:00
-- url     : https://prove2.me/submissions/4de1839e-7951-4785-8164-84a9ce3e8642

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_tailProd
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_listDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution : StatEDiag := by
  unfold StatEDiag
  intro A _ d _ _ S β t α
  dsimp only
  have hfac : ∀ i, (Matrix.diagonal (fun a => if S a then β a else 0) -
      α i • Matrix.diagonal (fun a => if S a then (1 : A) else 0)) =
      Matrix.diagonal (fun a => if S a then β a - α i else 0) := by
    intro i
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hS : S a <;> simp [hS]
    · simp [Matrix.diagonal_apply_ne _ hab]
  simp_rw [hfac]
  rw [listDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases hS : S a
  · simp only [hS, ↓reduceIte, one_mul]
    exact tailProd _ t
  · simp [hS]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
