-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.halfForce
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:16.323447+00:00
-- url     : https://prove2.me/submissions/75481a2c-0c77-45ca-8675-df185aedcef4

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_keyCm
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_det_of_cm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_S3x8_map_smul__256ab68aac63
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_of_sub_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_range_stable
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_div_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_rdiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_ldiv

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
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {ϖ : o} (hϖ : Irreducible ϖ) {j j' : Matrix (Idx r k) (Idx r k) o}
    {n n' : Matrix (Idx r k) (Idx r k) k0} {X : Matrix (Fin r) (Fin r) o}
    (hj : BT (j.map (IsLocalRing.residue o))) (hX : b31 j = ϖ • X)
    (hc : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl))
    (hj' : BT (j'.map (IsLocalRing.residue o))) (hn : IsN n) (hn' : IsN n')
    (e : n * j'.map (algebraMap o k0) = j.map (algebraMap o k0) * n') :
    Integral o (b33 n) ∧ Integral o (b11 n') ∧ Integral o (b23 n) ∧ Integral o (b12 n') ∧
      ∃ X' : Matrix (Fin r) (Fin r) o, b31 j' = ϖ • X' ∧ ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X' l hl) := by
  have hinj : Function.Injective (algebraMap o k0) := IsFractionRing.injective o k0
  have hϖ0 : algebraMap o k0 ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  obtain ⟨g11, g33, g22, g21, g31, g32⟩ := hn'
  obtain ⟨X', hX'⟩ := div_pi hϖ (b31 j') hj'.2.2.2.1
  obtain ⟨P, hP⟩ := div_pi hϖ (b21 j) hj.2.2.1
  obtain ⟨P', hP'⟩ := div_pi hϖ (b21 j') hj'.2.2.1
  obtain ⟨Q, hQ⟩ := div_pi hϖ (b32 j) hj.2.2.2.2.1
  obtain ⟨Q', hQ'⟩ := div_pi hϖ (b32 j') hj'.2.2.2.2.1
  have e31 := congrArg b31 e
  rw [block31_mul, block31_mul, h31, h32, g21, g31, block31_map, block31_map, hX, hX', map_smul', map_smul'] at e31
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
    Matrix.smul_mul] at e31
  have E31 := smul_right_injective _ hϖ0 e31
  obtain ⟨c33, c11, cc⟩ := keyCm (algebraMap o k0) hinj (algebraMap o k0).toAddMonoidHom.range
    range_stable X X' (b33 n) (b11 n') h33 g11 E31 (fun a b => ⟨_, rfl⟩) hc
  have i33 : Integral o (b33 n) := int_of_sub_one c33
  have i11 : Integral o (b11 n') := int_of_sub_one c11
  have hc' : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X' l hl) := fun l hl => by rw [cc]; exact hc l hl
  refine ⟨i33, i11, ?_, ?_, X', hX', hc'⟩
  · have e21 := congrArg b21 e
    rw [block21_mul, block21_mul, h21, h22, g21, g31, block21_map, block21_map, block31_map, hX', hP, hP', map_smul',
      map_smul', map_smul'] at e21
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.one_mul, ← smul_add] at e21
    have E21 := smul_right_injective _ hϖ0 e21
    refine int_rdiv (det_of_cm X' (hc' r le_rfl)) ?_
    rw [eq_sub_iff_add_eq'.2 E21]
    exact int_sub (int_mul (int_map _) i11) (int_map _)
  · have e32 := congrArg b32 e
    rw [block32_mul, block32_mul, h31, h32, g22, g32, block32_map, block32_map, block31_map, hX, hQ, hQ', map_smul',
      map_smul', map_smul'] at e32
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, ← smul_add] at e32
    have E32 := smul_right_injective _ hϖ0 e32
    refine int_ldiv (det_of_cm X (hc r le_rfl)) ?_
    rw [eq_sub_iff_add_eq.2 E32.symm]
    exact int_sub (int_mul i33 (int_map _)) (int_map _)
end Formalism.FourierDecayAlt.P.S3x8
