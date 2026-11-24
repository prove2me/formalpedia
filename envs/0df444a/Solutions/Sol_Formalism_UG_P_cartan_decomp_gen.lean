-- Prove2me | solution 1 for Formalism.UG.P.cartan_decomp_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:06:50.349277+00:00
-- url     : https://prove2.me/submissions/f6343abc-f1c4-479b-a1a0-fe2570b0181e

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Theorems.Thm_Formalism_UG_P_cartan_smith
import Theorems.Thm_Formalism_UG_P_cartan_sort
import Theorems.Thm_Formalism_UG_P_cartan_diag_units

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
namespace Formalism.UG.P
theorem _root_.solution [IsPrincipalIdealRing O] (val : Valuation L Γ)
    (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (ϖ : L) (hϖ0 : ϖ ≠ 0)
    (hU : ∀ x : L, x ≠ 0 → ∃ k : ℤ, val x = val ϖ ^ k) {m : ℕ} (g : GL (Fin m) L) (c : O)
    (hc : c ≠ 0) (hg : (c : L) • (g : Matrix (Fin m) (Fin m) L) ∈
      (RingHom.mapMatrix (m := Fin m) O.subtype).range) :
    ∃ a : Fin m → ℤ, Antitone a ∧ ∃ k₁ ∈ GLint (Fin m) O, ∃ k₂ ∈ GLint (Fin m) O,
      (g : Matrix (Fin m) (Fin m) L) = (k₁ : Matrix (Fin m) (Fin m) L) *
        Matrix.diagonal (fun i => ϖ ^ a i) * (k₂ : Matrix (Fin m) (Fin m) L) := by
  obtain ⟨G, hG⟩ := hg
  have hc' : (c : L) ≠ 0 := fun h => hc (Subtype.ext h)
  have hg0 : (g : Matrix (Fin m) (Fin m) L).det ≠ 0 := by
    have : (g : Matrix (Fin m) (Fin m) L).det * ((g⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one this
  have hdet : G.det ≠ 0 := by
    intro h0
    have : O.subtype G.det = 0 := by rw [h0, map_zero]
    rw [RingHom.map_det, hG, Matrix.det_smul] at this
    exact mul_ne_zero (pow_ne_zero _ hc') hg0 this
  obtain ⟨P, C, hP, hC, d, hd, hPdC⟩ := cartan_smith G hdet
  let PL := bc (n := Fin m) O.subtype (Matrix.nonsingInvUnit P hP)
  let CL := bc (n := Fin m) O.subtype (Matrix.nonsingInvUnit C hC)
  have hPL : (PL : Matrix (Fin m) (Fin m) L) = RingHom.mapMatrix O.subtype P := rfl
  have hCL : (CL : Matrix (Fin m) (Fin m) L) = RingHom.mapMatrix O.subtype C := rfl
  let d' : Fin m → L := fun i => (c : L)⁻¹ * (d i : L)
  have hd' : ∀ i, d' i ≠ 0 := fun i =>
    mul_ne_zero (inv_ne_zero hc') (fun h => hd i (Subtype.ext h))
  have hgd : (g : Matrix (Fin m) (Fin m) L) = (PL : Matrix (Fin m) (Fin m) L) *
      Matrix.diagonal d' * (CL : Matrix (Fin m) (Fin m) L) := by
    have hX : (g : Matrix (Fin m) (Fin m) L) = (c : L)⁻¹ • ((c : L) • (g : Matrix (Fin m) (Fin m) L)) := by
      rw [smul_smul, inv_mul_cancel₀ hc', one_smul]
    have hD : Matrix.diagonal d' = (c : L)⁻¹ • RingHom.mapMatrix O.subtype (Matrix.diagonal d) := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.smul_apply,
        smul_eq_mul, d']
      split_ifs <;> simp
    rw [hX, ← hG, hPdC, map_mul, map_mul, hPL, hCL, hD, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨a, U, hUm, hUe⟩ := cartan_diag_units O val hO ϖ hϖ0 hU d' hd'
  obtain ⟨a', ha', S₁, h₁, S₂, h₂, hS⟩ := cartan_sort O ϖ a
  refine ⟨a', ha', PL * U * S₁, mul_mem (mul_mem ⟨_, rfl⟩ hUm) h₁, S₂ * CL,
    mul_mem h₂ ⟨_, rfl⟩, ?_⟩
  rw [hgd, hUe, hS]
  simp only [Units.val_mul, Matrix.mul_assoc]
end Formalism.UG.P
