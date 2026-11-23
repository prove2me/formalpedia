-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.mem_latZ_rank1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:09.270803+00:00
-- url     : https://prove2.me/submissions/e9779a7e-a0da-4704-9bf2-8d1bf0301aea

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mat_add_vecMulVec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_smul_coe
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
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (m : Fin n → R)
    (β : Fin n → K) (hβ : ∀ b, β b ∈ R) (h0 : β ⬝ᵥ (Z⁻¹ *ᵥ coeLin R m) = 0) (x : Fin n → R) :
    x ∈ latZ R (Z + vecMulVec (coeLin R m) β) ↔
      ∃ r : R, (r : K) = β ⬝ᵥ (Z⁻¹ *ᵥ coeLin R x) ∧ x - r • m ∈ latZ R Z := by
  rw [mem_latZ]
  constructor
  · rintro ⟨t, e⟩
    rw [mat_add_vecMulVec] at e
    have hmem : β ⬝ᵥ coeLin R t ∈ R := by
      simp only [dotProduct]
      refine R.sum_mem fun b _ => ?_
      rw [coeLin_apply]
      exact R.mul_mem (hβ b) (t b).2
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · show β ⬝ᵥ coeLin R t = _
      rw [← e, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd,
        Matrix.one_mulVec, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, h0, smul_zero,
        add_zero]
    · rw [mem_latZ]
      refine ⟨t, ?_⟩
      rw [map_sub, map_smul, ← e, A5x2.smul_coe]
      simp
  · rintro ⟨r, hr, hx⟩
    obtain ⟨t, e⟩ := (mem_latZ R _ _).1 hx
    rw [map_sub, map_smul, A5x2.smul_coe] at e
    have ht : coeLin R t = Z⁻¹ *ᵥ coeLin R x - (r : K) • (Z⁻¹ *ᵥ coeLin R m) := by
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_sub, ← e, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
    have hb : β ⬝ᵥ coeLin R t = (r : K) := by
      rw [ht, dotProduct_sub, dotProduct_smul, h0, smul_zero, sub_zero, hr]
    refine ⟨t, ?_⟩
    rw [mat_add_vecMulVec, hb, e]
    simp
end Formalism.FourierDecayAlt.P.A5x9
