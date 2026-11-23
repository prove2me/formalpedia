-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.centreForcing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:35.442808+00:00
-- url     : https://prove2.me/submissions/a50054a5-92c2-41a0-a1a1-a85c5f476e28

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_uniqCm
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_cm_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_det_of_cm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_S3x8_map_smul__256ab68aac63
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_div_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_res_pi

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
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution : CentreForcing := by
  intro o _ _ _ k0 _ _ _ ϖ hϖ r ξ₁ ξ₂ j₁₃ X y₁ y₂ y₃ S S' hξ₁ hξ₂ hX hy₁ hy₂ e₁ e₂ e₃
  have hinj : Function.Injective (algebraMap o k0) := IsFractionRing.injective o k0
  have hϖ0 : algebraMap o k0 ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hXd : IsUnit X.det := det_of_cm X (hX r le_rfl)
  have X1 : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXd
  have X2 : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hXd
  rw [map_smul'] at e₁ e₂ e₃
  simp only [← RingHom.mapMatrix_apply] at e₁ e₂ e₃
  generalize hΦ : (algebraMap o k0).mapMatrix (m := Fin r) = Φ at e₁ e₂ e₃
  have Φsmul : ∀ (c : o) (x : Matrix (Fin r) (Fin r) o), Φ (c • x) = algebraMap o k0 c • Φ x := by
    intro c x; rw [← hΦ]; exact map_smul' _ c x
  have Φinj : Function.Injective Φ := by
    rw [← hΦ]; exact Matrix.map_injective hinj
  have X1φ : Φ X * Φ X⁻¹ = 1 := by rw [← map_mul, X1, map_one]
  have X2φ : Φ X⁻¹ * Φ X = 1 := by rw [← map_mul, X2, map_one]
  have s1 : algebraMap o k0 ϖ • S = Φ (ξ₁ - y₁) * Φ X⁻¹ := by
    have : Φ (ξ₁ - y₁) = algebraMap o k0 ϖ • (S * Φ X) := by
      rw [map_sub, e₁, mul_smul_comm]; abel
    rw [this, smul_mul_assoc, mul_assoc, X1φ, mul_one]
  have s2 : algebraMap o k0 ϖ • S' = Φ X⁻¹ * Φ (y₂ - ξ₂) := by
    have : Φ (y₂ - ξ₂) = algebraMap o k0 ϖ • (Φ X * S') := by
      rw [map_sub, e₂, smul_mul_assoc]; abel
    rw [this, mul_smul_comm, ← mul_assoc, X2φ, one_mul]
  have rel : ϖ • (y₃ - j₁₃) = y₁ * X⁻¹ * y₂ - ξ₁ * X⁻¹ * ξ₂ := by
    apply Φinj
    calc Φ (ϖ • (y₃ - j₁₃)) = algebraMap o k0 ϖ • (-(S * Φ ξ₂) + Φ y₁ * S') := by
          rw [Φsmul, map_sub, e₃, ← e₁]; congr 1; abel
      _ = -((algebraMap o k0 ϖ • S) * Φ ξ₂) + Φ y₁ * (algebraMap o k0 ϖ • S') := by
          rw [smul_add, smul_neg, smul_mul_assoc, mul_smul_comm]
      _ = Φ (y₁ * X⁻¹ * y₂ - ξ₁ * X⁻¹ * ξ₂) := by
          rw [s1, s2]; simp only [map_sub, map_mul]; noncomm_ring

  have hres : ∀ x : Matrix (Fin r) (Fin r) o, (ϖ • x).map (IsLocalRing.residue o) = 0 := by
    intro x; rw [map_smul', res_pi hϖ, zero_smul]
  have rel' : y₁.map (IsLocalRing.residue o) * X⁻¹.map (IsLocalRing.residue o) *
        y₂.map (IsLocalRing.residue o) =
      ξ₁.map (IsLocalRing.residue o) * X⁻¹.map (IsLocalRing.residue o) *
        ξ₂.map (IsLocalRing.residue o) := by
    have := congrArg (fun m => m.map (IsLocalRing.residue o)) rel
    simp only [hres] at this
    simp only [← RingHom.mapMatrix_apply, map_sub, map_mul] at this ⊢
    exact (sub_eq_zero.1 this.symm)
  have xx : X.map (IsLocalRing.residue o) * X⁻¹.map (IsLocalRing.residue o) = 1 := by
    rw [← Matrix.map_mul, X1]; simp
  have xix : X⁻¹.map (IsLocalRing.residue o) * X.map (IsLocalRing.residue o) = 1 := by
    rw [← Matrix.map_mul, X2]; simp
  have hXr : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm (X.map (IsLocalRing.residue o)) l hl) := by
    intro l hl; rw [cm_map]; exact (hX l hl).map _
  generalize X.map (IsLocalRing.residue o) = x at xx xix hXr
  generalize X⁻¹.map (IsLocalRing.residue o) = xi at xx xix rel'
  have key2 : ξ₁.map (IsLocalRing.residue o) = y₁.map (IsLocalRing.residue o) ∧
      ξ₂.map (IsLocalRing.residue o) = y₂.map (IsLocalRing.residue o) := by
    generalize ξ₁.map (IsLocalRing.residue o) = a at hξ₁ rel' ⊢
    generalize y₁.map (IsLocalRing.residue o) = b at hy₁ rel' ⊢
    generalize ξ₂.map (IsLocalRing.residue o) = c at hξ₂ rel' ⊢
    generalize y₂.map (IsLocalRing.residue o) = d at hy₂ rel' ⊢
    have ua : IsUnit a.det := by rw [isUpUni_det _ hξ₁]; exact isUnit_one
    have ud : IsUnit d.det := by rw [isUpUni_det _ hy₂]; exact isUnit_one
    have aa : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ua
    have aa' : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a ua
    have dd : d * d⁻¹ = 1 := Matrix.mul_nonsing_inv d ud
    have dd' : d⁻¹ * d = 1 := Matrix.nonsing_inv_mul d ud
    have h1 : a⁻¹ * b * xi = xi * c * d⁻¹ := by
      calc a⁻¹ * b * xi = a⁻¹ * (b * xi * d) * d⁻¹ := by simp only [mul_assoc, dd, mul_one]
        _ = a⁻¹ * (a * xi * c) * d⁻¹ := by rw [rel']
        _ = xi * c * d⁻¹ := by simp only [← mul_assoc, aa, one_mul]
    have h2 : c * d⁻¹ * x = x * (a⁻¹ * b) := by
      calc c * d⁻¹ * x = x * (xi * c * d⁻¹) * x := by simp only [← mul_assoc, xx, one_mul]
        _ = x * (a⁻¹ * b * xi) * x := by rw [h1]
        _ = x * (a⁻¹ * b) := by simp only [mul_assoc, xix, mul_one]
    obtain ⟨q1, p1⟩ := uniqCm x (c * d⁻¹) (a⁻¹ * b) (isUpUni_mul _ hξ₂ (isUpUni_inv _ hy₂))
      (isUpUni_mul _ (isUpUni_inv _ hξ₁) hy₁) h2 hXr
    constructor
    · calc a = a * (a⁻¹ * b) := by rw [p1, mul_one]
        _ = b := by rw [← mul_assoc, aa', one_mul]
    · calc c = c * d⁻¹ * d := by rw [mul_assoc, dd', mul_one]
        _ = d := by rw [q1, one_mul]
  obtain ⟨k1, k2⟩ := key2
  obtain ⟨a', ha'⟩ := div_pi hϖ (ξ₁ - y₁) (by
    simp only [← RingHom.mapMatrix_apply, map_sub] at k1 ⊢; rw [k1, sub_self])
  obtain ⟨b', hb'⟩ := div_pi hϖ (y₂ - ξ₂) (by
    simp only [← RingHom.mapMatrix_apply, map_sub] at k2 ⊢; rw [k2, sub_self])
  constructor
  · refine ⟨a' * X⁻¹, ?_⟩
    rw [ha', Φsmul, smul_mul_assoc] at s1
    have := smul_right_injective _ hϖ0 s1
    rw [this, ← map_mul, ← hΦ]; rfl
  · refine ⟨X⁻¹ * b', ?_⟩
    rw [hb', Φsmul, mul_smul_comm] at s2
    have := smul_right_injective _ hϖ0 s2
    rw [this, ← map_mul, ← hΦ]; rfl
end Formalism.FourierDecayAlt.P.S3x8
