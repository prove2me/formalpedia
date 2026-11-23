-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.invOm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:36.761592+00:00
-- url     : https://prove2.me/submissions/3f784d50-4f24-4fa8-ae02-e83527110317

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_invCm
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_cm_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_cm_neg
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_S3x8_map_smul__256ab68aac63
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_div_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_res_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_one_block31
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_bt_rinv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {r k : ℕ}
variable [IsDomain o] [IsDiscreteValuationRing o] [IsFractionRing o k0]
omit [IsFractionRing o k0]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {ϖ : o} (hϖ : Irreducible ϖ) {j : Matrix (Idx r k) (Idx r k) o}
    {X : Matrix (Fin r) (Fin r) o} (hd : IsUnit j.det)
    (hj : BT (j.map (IsLocalRing.residue o))) (hX : b31 j = ϖ • X)
    (hc : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)) :
    BT (j⁻¹.map (IsLocalRing.residue o)) ∧
      ∃ Y : Matrix (Fin r) (Fin r) o, b31 j⁻¹ = ϖ • Y ∧ ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm Y l hl) := by
  have j1 : j * j⁻¹ = 1 := Matrix.mul_nonsing_inv j hd
  have hi : BT (j⁻¹.map (IsLocalRing.residue o)) := bt_rinv hj (by rw [← Matrix.map_mul, j1]; simp)
  refine ⟨hi, ?_⟩
  obtain ⟨Y, hY⟩ := div_pi hϖ (b31 j⁻¹) hi.2.2.2.1
  obtain ⟨Q, hQ⟩ := div_pi hϖ (b21 j⁻¹) hi.2.2.1
  obtain ⟨P, hP⟩ := div_pi hϖ (b32 j) hj.2.2.2.2.1
  refine ⟨Y, hY, ?_⟩
  have e31 := congrArg b31 j1
  rw [block31_mul, one_block31, hX, hP, hQ, hY] at e31
  have e31' : ϖ • (X * b11 j⁻¹ + ϖ • (P * Q) + b33 j * Y) = ϖ • (0 : Matrix (Fin r) (Fin r) o) := by
    rw [smul_zero, ← e31]
    simp only [smul_add, Matrix.mul_smul, Matrix.smul_mul]
  have E := smul_right_injective _ hϖ.ne_zero e31'
  have E' := congrArg (fun m => m.map (IsLocalRing.residue o)) E
  simp only [← RingHom.mapMatrix_apply, map_add, map_mul, map_zero] at E'
  simp only [RingHom.mapMatrix_apply, map_smul', res_pi hϖ, zero_smul, add_zero] at E'
  have E2 : (b33 j).map (IsLocalRing.residue o) * Y.map (IsLocalRing.residue o) =
      (-X.map (IsLocalRing.residue o)) * (b11 j⁻¹).map (IsLocalRing.residue o) := by
    rw [neg_mul]; exact eq_neg_of_add_eq_zero_right E'
  have hu : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm (-X.map (IsLocalRing.residue o)) l hl) := by
    intro l hl
    rw [cm_neg, cm_map]
    exact ((isUnit_one.neg).pow l).mul ((hc l hl).map _)
  have := invCm _ _ _ _ hj.2.1 hi.1 E2 hu
  intro l hl
  refine (isUnit_map_iff (IsLocalRing.residue o) _).1 ?_
  rw [← cm_map, this]
  exact hu l hl
end Formalism.FourierDecayAlt.P.S3x8
