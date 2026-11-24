-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:45:40.617974+00:00
-- url     : https://prove2.me/submissions/2261cf78-6693-4bd2-a2e9-aea99b8401c8

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_hpk_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_ell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromCols
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromRows
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_lowW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_subS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_supS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_continuous_psi_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_cornerA
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_cornerB
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_ell
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromCols
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromRows
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_lowW
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_strictUpper
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_subS
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_supS
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_upper
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.continuous_psi_comp
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (v : H) :
    ContinuousOn (fun g => σ g v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, hPunit⟩, hDS⟩ := hσ
  have hc := hDS.2.2.1.2.2 v
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hmaps : Set.MapsTo (fun g : Mx k r => P * g * P⁻¹) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
      (PI.UpqRep.UJset ε) := by
    intro g hg
    show (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹) = PI.UpqRep.Jm ε
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hJ : (P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹ = PI.UpqRep.Jm ε := by
      rw [← hpk_eq, ← hPJ]
      have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
      have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
      calc (P⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * P⁻¹
          = ((P⁻¹)ᴴ * Pᴴ) * PI.UpqRep.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
        _ = PI.UpqRep.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
    have hPPh : Pᴴ * (P⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one]
    calc (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹)
        = (P⁻¹)ᴴ * gᴴ * Pᴴ * ((P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹) * (P * g * P⁻¹) := by
          rw [hJ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pᴴ (P⁻¹)ᴴ, hPPh, Matrix.one_mul]
          rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
      _ = PI.UpqRep.Jm ε := by rw [hg', hJ]
  have hcont : Continuous (fun g : Mx k r => P * g * P⁻¹) := by fun_prop
  have := hc.comp hcont.continuousOn hmaps
  refine this.congr ?_
  intro g _
  show σ g v = σ (P⁻¹ * (P * g * P⁻¹) * P) v
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.S3dx4
