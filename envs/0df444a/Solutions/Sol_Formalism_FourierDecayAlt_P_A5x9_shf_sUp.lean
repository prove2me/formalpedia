-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.shf_sUp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:20.589033+00:00
-- url     : https://prove2.me/submissions/28b92954-d622-4333-aee1-cbc1994bfbe9

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
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) (r c : Fin n) (hr : r.val = k) (hc : c.val = k + 1) :
    sUp (1 + vecMulVec ξ β) = ξ r * β c := by
  unfold sUp
  rw [Finset.sum_eq_single r]
  · have h : r.val + 1 < n := by rw [hr, ← hc]; exact c.2
    rw [dif_pos h]
    have e : (⟨r.val + 1, h⟩ : Fin n) = c := Fin.ext (by simp [hr, hc])
    rw [e]
    have hne : r ≠ c := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, vecMulVec_apply]
  · intro j _ hj
    by_cases h : j.val + 1 < n
    · rw [dif_pos h]
      have hne : j ≠ ⟨j.val + 1, h⟩ := by
        intro h'
        have := congrArg Fin.val h'
        simp at this
      have h0 : ξ j * β ⟨j.val + 1, h⟩ = 0 := by
        rcases lt_trichotomy j.val k with h1 | h1 | h1
        · rw [hβ ⟨j.val + 1, h⟩ (by simp only; omega), mul_zero]
        · exact absurd (Fin.ext (h1.trans hr.symm)) hj
        · rw [hξ j h1, zero_mul]
      rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, vecMulVec_apply, h0]
    · rw [dif_neg h]
  · simp
end Formalism.FourierDecayAlt.P.A5x9
