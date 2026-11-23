-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.shf_isP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:18.007832+00:00
-- url     : https://prove2.me/submissions/95aca57d-b1f7-4e55-8df6-e17f93a333be

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ξ β : Fin n → K) (hξ : ∀ j : Fin n, k < j.val → ξ j = 0)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) : IsP R k (1 + vecMulVec ξ β) := by
  have key : ∀ a b : Fin n, (k < a.val ∨ b.val ≤ k) → vecMulVec ξ β a b = 0 := by
    intro a b h
    rcases h with h | h
    · simp [vecMulVec_apply, hξ a h]
    · simp [vecMulVec_apply, hβ b h]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    have h0 : vecMulVec ξ β a b = 0 := by
      apply key
      have := Fin.lt_def.1 hab'
      omega
    rw [Matrix.add_apply, h0, add_zero, Matrix.one_apply_ne hab'.ne']
  · intro a
    have h0 : vecMulVec ξ β a a = 0 := key a a (by omega)
    rw [Matrix.add_apply, h0, add_zero, Matrix.one_apply_eq]
  · intro a b h
    rw [Matrix.add_apply, key a b h, add_zero]
    by_cases hab : a = b
    · rw [hab, Matrix.one_apply_eq]; exact R.one_mem
    · rw [Matrix.one_apply_ne hab]; exact R.zero_mem
end Formalism.FourierDecayAlt.P.A5x9
