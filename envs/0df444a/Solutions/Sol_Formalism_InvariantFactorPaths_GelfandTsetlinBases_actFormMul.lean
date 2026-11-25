-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.actFormMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:04:59.221885+00:00
-- url     : https://prove2.me/submissions/7eb2461a-841f-430e-a364-6da63ee05eb3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_add
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actFormWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_form_induction
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_oneF

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : FactX2mul := by
  intro R _ n K m m'
  constructor
  · refine form_induction (P := fun K => actF K 1 = K) ?_ ?_ ?_ ?_ K
    · exact actF_oneF 1
    · intro K K' h h'
      try dsimp only at h h' ⊢
      rw [actF_add, h, h']
    · intro c K h
      try dsimp only at h ⊢
      rw [actF_smul, h]
    · intro K X h
      try dsimp only at h ⊢
      rw [actFormWedge R n K X 1, h, Matrix.vecMul_one]
  · refine form_induction (P := fun K => actF (actF K m) m' = actF K (m * m')) ?_ ?_ ?_ ?_ K
    · try dsimp only
      rw [actF_oneF, actF_oneF, actF_oneF]
    · intro K K' h h'
      try dsimp only at h h' ⊢
      rw [actF_add, actF_add, actF_add, h, h']
    · intro c K h
      try dsimp only at h ⊢
      rw [actF_smul, actF_smul, actF_smul, h]
    · intro K X h
      try dsimp only at h ⊢
      rw [actFormWedge R n K X m, actFormWedge R n (actF K m) (Matrix.vecMul X m) m', h,
        actFormWedge R n K X (m * m'), Matrix.vecMul_vecMul]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
