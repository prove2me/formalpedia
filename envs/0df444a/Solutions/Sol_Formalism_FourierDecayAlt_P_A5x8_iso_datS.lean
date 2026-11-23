-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iso_datS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:58.788881+00:00
-- url     : https://prove2.me/submissions/e6ef791a-6fd8-4ae7-b75f-7dd7501ee0e9

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_top_vec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_bot_vec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_Phi_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_piS_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_affine_form_on_vector
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K) {m N : ℕ} (hN : N = m + 1)
  (Z : Matrix (Fin m) (Fin m) K) (hZ : IsUnit Z.det) (ξ η : Fin m → K) (c : Kˣ)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (hξ : ∀ j, (ξ ᵥ* Z) j ∈ R) (α : coker R Z →ₗ[R] KR R)
    (hα : ∀ v, α (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ξ ⬝ᵥ coeLin R v)) :
    iso_Dat R (iso_M R hN Z ξ) (coker R Z) 1 (iso_Phi R hN Z ξ)
      (iso_piS R hN Z ξ) (Submodule.Quotient.mk (iso_vec hN 0 1)) (-α) where
  surj y := by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk (iso_vec hN a 0), by rw [iso_piS_mk, iso_top_vec]⟩
  ker x hx := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [iso_piS_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨a, ha⟩ := (Formalism.DoubleCosetMeasures.P.mem_latZ R Z _).1 hx
    have hmem : ξ ᵥ* Z ⬝ᵥ coeLin R a ∈ R := by
      refine R.sum_mem fun j _ => R.mul_mem (hξ j) ?_
      rw [Formalism.DoubleCosetMeasures.P.coeLin_apply]; exact (a j).2
    refine ⟨iso_bot R hN x - ⟨_, hmem⟩, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, iso_mem_ker]
    have h3 : iso_top R hN (x - (iso_bot R hN x - ⟨_, hmem⟩) • iso_vec hN 0 1) =
        iso_top R hN x := by
      rw [map_sub, map_smul, iso_top_vec, smul_zero, sub_zero]
    refine ⟨by rw [h3]; exact hx, ?_⟩
    rw [affine_form_apply, h3, map_sub, map_smul, iso_bot_vec, ← ha, Matrix.dotProduct_mulVec]
    simp
  pg := by
    rw [iso_piS_mk, iso_top_vec]; rfl
  Pg := by
    rw [iso_Phi_mk, affine_form_on_vector]; simp
  lam_pi x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [iso_piS_mk, LinearMap.neg_apply, hα, iso_Phi_mk, affine_form_apply, ← Submodule.Quotient.mk_neg,
      Submodule.Quotient.eq]
    refine ⟨-iso_bot R hN x, ?_⟩
    have h0 : (algebraMap R K) (iso_bot R hN x) = (iso_bot R hN x : K) := rfl
    simp only [map_neg, Algebra.linearMap_apply, h0, inv_one, Units.val_one, one_mul]
    ring
end Formalism.FourierDecayAlt.P.A5x8
