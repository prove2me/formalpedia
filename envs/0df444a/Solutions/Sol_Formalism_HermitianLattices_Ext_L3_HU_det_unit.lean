-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.det_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:07.54042+00:00
-- url     : https://prove2.me/submissions/8b620d06-259d-4003-8583-558e032369fd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StepIdentity
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Newton_det_one_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_pow_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hHS : Ent S H)
    (hES : Ent S E) {e k : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hk : e + 1 ≤ k)
    {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) :
    X.det ≠ 0 ∧ X.det⁻¹ ∈ S := by
  have hW : Ent S (ϖ ^ (k - e - 1) • (Z * E)) := Ent.smul (S.pow_mem hS.mem _) (hZ.mul hES)
  obtain ⟨s, hs, hdet⟩ := Newton.det_one_add hS.mem hW
  have hmat : Xᴴ * H * X * E = ϖ ^ e • (1 + ϖ • (ϖ ^ (k - e - 1) • (Z * E))) := by
    rw [hXZ, add_mul, hHE, smul_mul_assoc, smul_add, smul_smul, smul_smul, ← pow_succ, ← pow_add,
      show e + 1 + (k - e - 1) = k by omega]
  have h1 := congrArg Matrix.det hmat
  rw [det_mul, det_mul, det_mul, det_smul, hdet, det_conjTranspose] at h1
  have h2 := congrArg Matrix.det hHE
  rw [det_mul, det_smul, det_one, mul_one] at h2
  have hc : (ϖ ^ e) ^ Fintype.card n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hS.ne)
  have h3 : star X.det * X.det = 1 + ϖ * s := by
    apply mul_right_cancel₀ hc
    linear_combination h1 - star X.det * X.det * h2
  obtain ⟨hne, hinv⟩ := hS.rad s hs
  have hX0 : X.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h3
    exact hne h3.symm
  have hsX : star X.det ≠ 0 := star_ne_zero.mpr hX0
  refine ⟨hX0, ?_⟩
  have e4 : X.det⁻¹ = star X.det * (1 + ϖ * s)⁻¹ := by
    rw [← h3, mul_inv, ← mul_assoc, mul_inv_cancel₀ hsX, one_mul]
  rw [e4]
  exact S.mul_mem (hS.star_mem _ hX.det) hinv
end Formalism.HermitianLattices.Ext.L3.HU
