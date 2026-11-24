-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Newton.step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:08.018225+00:00
-- url     : https://prove2.me/submissions/fdf38288-a6a8-430b-b72a-ecc703f26bc9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StepIdentity
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Newton_step_identity
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_conjTranspose
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_sub
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
open Formalism.HermitianLattices.Ext.L3.HU.Newton
namespace Formalism.HermitianLattices.Ext.L3.HU.Newton
theorem _root_.solution (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hES : Ent S E) {e k : ℕ}
    (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hk : e + 1 ≤ k)
    {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) :
    ∃ D Z' : Matrix n n K, Ent S D ∧ Ent S Z' ∧
      (X + ϖ ^ (k - e) • D)ᴴ * H * (X + ϖ ^ (k - e) • D) = H + ϖ ^ (k + 1) • Z' := by
  obtain ⟨τ, hτ, hτ1⟩ := hS.tr
  have hstar : ∀ m : ℕ, star (ϖ ^ m) = ϖ ^ m := fun m => by rw [star_pow, hS.fix]
  have hZH : Zᴴ = Z := by
    have h1 : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
    rw [hXZ, conjTranspose_add, hH, conjTranspose_smul, hstar] at h1
    have h2 : ϖ ^ k • Zᴴ = ϖ ^ k • Z := add_left_cancel h1
    exact smul_right_injective _ (pow_ne_zero k hS.ne) h2
  have hYent : Ent S (E * (τ • Z)) := hES.mul (Ent.smul hτ hZ)
  have hYc : Ent S (E * (τ • Z))ᴴ := Ent.conjTranspose hS.star_mem hYent
  have hab : ϖ ^ (k - e) * ϖ ^ e = ϖ ^ k := by rw [← pow_add, Nat.sub_add_cancel (by omega : e ≤ k)]
  have hG : Xᴴ * H * X = H + (ϖ ^ (k - e) * ϖ ^ e) • Z := by rw [hab]; exact hXZ
  have hHY : H * (E * (τ • Z)) = ϖ ^ e • (τ • Z) := by
    rw [← Matrix.mul_assoc, hHE, smul_mul_assoc, one_mul]
  have hEH : Eᴴ * H = ϖ ^ e • (1 : Matrix n n K) := by
    have h3 := congrArg conjTranspose hHE
    rw [conjTranspose_mul, hH, conjTranspose_smul, conjTranspose_one, hstar] at h3
    exact h3
  have hYH : (E * (τ • Z))ᴴ * H = ϖ ^ e • (star τ • Z) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, hEH, conjTranspose_smul, hZH, mul_smul_comm, mul_one]
  have hV : star τ • Z + τ • Z = Z := by rw [← add_smul, add_comm, hτ1, one_smul]
  have hid := Newton.step_identity Xᴴ H X (E * (τ • Z)) (E * (τ • Z))ᴴ Z (star τ • Z) (τ • Z)
    (ϖ ^ (k - e)) (ϖ ^ e) hG hHY hYH hV
  refine ⟨-(X * (E * (τ • Z))), ϖ ^ (k - e - 1) • (-(Z * (E * (τ • Z))) - (E * (τ • Z))ᴴ * Z +
    (E * (τ • Z))ᴴ * (τ • Z) + ϖ ^ (k - e) • ((E * (τ • Z))ᴴ * Z * (E * (τ • Z)))), (hX.mul hYent).neg,
    Ent.smul (S.pow_mem hS.mem _) ((((hZ.mul hYent).neg.sub (hYc.mul hZ)).add
      (hYc.mul (Ent.smul hτ hZ))).add (Ent.smul (S.pow_mem hS.mem _) ((hYc.mul hZ).mul hYent))), ?_⟩
  have e1 : X + ϖ ^ (k - e) • -(X * (E * (τ • Z))) = X - ϖ ^ (k - e) • (X * (E * (τ • Z))) := by
    rw [smul_neg, ← sub_eq_add_neg]
  have e2 : (X - ϖ ^ (k - e) • (X * (E * (τ • Z))))ᴴ =
      Xᴴ - ϖ ^ (k - e) • ((E * (τ • Z))ᴴ * Xᴴ) := by
    rw [conjTranspose_sub, conjTranspose_smul, hstar, conjTranspose_mul]
  have hp : ϖ ^ (k - e) * ϖ ^ (k - e) * ϖ ^ e = ϖ ^ (k + 1) * ϖ ^ (k - e - 1) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [e1, e2, hid, smul_smul, hp]
end Formalism.HermitianLattices.Ext.L3.HU.Newton
