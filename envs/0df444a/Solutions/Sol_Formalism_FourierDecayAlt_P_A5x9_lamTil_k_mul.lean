-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.lamTil_k_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:37.099382+00:00
-- url     : https://prove2.me/submissions/fa8066d2-23b7-43db-9d19-3991672a4cfb

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_apply
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_big
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_fin
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
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (x : Fin n → R)
    (h0 : abelian₂ R k Z₀ x = 0) : lamTil R (Z₀ * p) k x = lamTil R Z₀ k x := by
  by_cases hk : k < n
  · have e1 := A5x2.lamTil_fin R (Z₀ * p) ⟨k, hk⟩ x
    have e2 := A5x2.lamTil_fin R Z₀ ⟨k, hk⟩ x
    simp only at e1 e2
    rw [e1, e2, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    rw [Lam_apply] at h0
    generalize Z₀⁻¹ *ᵥ coeLin R x = y at h0 ⊢
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]
    · rw [hp.2.1.2, one_mul]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [up_zero hp.2.1 h, zero_mul]
      · have h2 := congrFun h0 b
        have hkb : k < b.val := Fin.lt_def.1 h
        simp only [msk, if_pos hkb, Pi.zero_apply] at h2
        rw [h2, mul_zero]
    · simp
  · rw [A5x2.lamTil_big R _ k (by omega), A5x2.lamTil_big R _ k (by omega)]
end Formalism.FourierDecayAlt.P.A5x9
