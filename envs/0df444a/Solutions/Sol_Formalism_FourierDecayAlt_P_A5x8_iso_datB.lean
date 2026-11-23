-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iso_datB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:28.69887+00:00
-- url     : https://prove2.me/submissions/f24ed318-bad9-47bc-8c7c-72b67393dc2f

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_piB_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_affine_form_on_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_lamLin_big
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_muZ_mk
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
theorem _root_.solution (b : Fin m → R) (hb : coeLin R b = Z *ᵥ η) (s : R)
    (hs : (s : K) = ξ ⬝ᵥ (Z *ᵥ η) + (c : K)) :
    iso_Dat R (iso_M R hN Z ξ) (coker R (bigZ hN Z ξ η (c : K))) c (iso_Phi R hN Z ξ)
      (iso_piB R hN Z ξ η (c : K)) (Submodule.Quotient.mk (iso_vec hN b s))
      (A5x6.muZ R (bigZ hN Z ξ η (c : K)) (iso_bigZ_det hN Z hZ ξ η c)) where
  surj y := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  ker x hx := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [iso_piB_mk, Submodule.Quotient.mk_eq_zero, Formalism.DoubleCosetMeasures.P.mem_latZ] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨iso_bot R hN y, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, iso_mem_ker]
    rw [← iso_eta R hN y, iso_coeLin_vec, bigZ, iso_blkM_mulVec, ← iso_eta R hN x,
      iso_coeLin_vec] at hy
    have h1 : Z *ᵥ coeLin R (iso_top R hN y) + (iso_bot R hN y : K) • Z *ᵥ η =
        coeLin R (iso_top R hN x) := by
      funext i
      have := congrFun hy (eN hN (Sum.inl i))
      rwa [iso_vec_inl, iso_vec_inl] at this
    have h2 : ξ ᵥ* Z ⬝ᵥ coeLin R (iso_top R hN y) +
        (ξ ⬝ᵥ Z *ᵥ η + (c : K)) * (iso_bot R hN y : K) = (iso_bot R hN x : K) := by
      have := congrFun hy (eN hN (Sum.inr ()))
      rwa [iso_vec_inr, iso_vec_inr] at this
    have h3 : coeLin R (iso_top R hN (x - iso_bot R hN y • iso_vec hN b s)) =
        Z *ᵥ coeLin R (iso_top R hN y) := by
      rw [map_sub, map_sub, map_smul, map_smul, iso_top_vec, hb, ← h1]
      have : iso_bot R hN y • Z *ᵥ η = (iso_bot R hN y : K) • Z *ᵥ η := rfl
      rw [this]; abel
    refine ⟨(Formalism.DoubleCosetMeasures.P.mem_latZ R Z _).2 ⟨_, h3.symm⟩, ?_⟩
    rw [affine_form_apply, h3, map_sub, map_smul, iso_bot_vec, ← Matrix.dotProduct_mulVec] at *
    push_cast
    rw [← h2]
    simp only [smul_eq_mul, Subring.coe_mul, hs]
    ring
  pg := by
    rw [iso_piB_mk, Submodule.Quotient.mk_eq_zero, Formalism.DoubleCosetMeasures.P.mem_latZ]
    refine ⟨iso_vec hN 0 1, ?_⟩
    rw [iso_coeLin_vec, iso_coeLin_vec, bigZ, iso_blkM_mulVec, hb, hs]
    simp
  Pg := by
    rw [iso_Phi_mk, affine_form_on_vector, hs, hb]; ring
  lam_pi x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [iso_piB_mk, A5x6.muZ_mk, iso_lamLin_big R hN Z hZ, iso_Phi_mk]
end Formalism.FourierDecayAlt.P.A5x8
