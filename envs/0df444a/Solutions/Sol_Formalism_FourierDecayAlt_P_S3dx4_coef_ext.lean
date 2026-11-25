-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.coef_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:41:33.487653+00:00
-- url     : https://prove2.me/submissions/6a588024-dae7-4e99-aaa7-99cb4ad17ae0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbConvDDOfDecDD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMemMeasurableSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res


section
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
namespace Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
private theorem conj_mem_lemma {ε : Fin (2 * r + k + 1) → Bool} {P a : Mx k r}
    (h1 : P * P⁻¹ = 1) (hPJ : Pᴴ * PI.UpqRep.Jm ε * P = PI.UpqRep.Hpk k r)
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    P * a * P⁻¹ ∈ PI.UpqRep.UJset ε := by
  have ha' : aᴴ * PI.UpqRep.Hpk k r * a = PI.UpqRep.Hpk k r := ha
  have hc : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (P * a * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * a * P⁻¹) = PI.UpqRep.Jm ε
  calc (P * a * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * a * P⁻¹)
        = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * a) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * P⁻¹ := by rw [hPJ, ha']
      _ = (P⁻¹)ᴴ * Pᴴ * PI.UpqRep.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = PI.UpqRep.Jm ε := by rw [hc, h1, Matrix.one_mul, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.S3dx4
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (v x : H) :
    ∃ e : Mx k r → ℂ, Continuous e ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e g = ⟪v, σ g x⟫_ℂ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, hDS⟩ := hds
  obtain ⟨-, -, ⟨-, -, hcontU⟩, -⟩ := hDS
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have key : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      h2, Matrix.one_mul, Matrix.mul_one]
  have hφ : Continuous fun g : Mx k r => P * g * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hcont : ContinuousOn (fun g : Mx k r => σ g x) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    have hc := (hcontU x).comp hφ.continuousOn (fun _ hg => conj_mem_lemma h1 hPJ hg)
    refine hc.congr fun g _ => ?_
    simp only [Function.comp_apply, key]
  have hid : Continuous fun g : Mx k r => g := continuous_id
  have hcl : IsClosed (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    show IsClosed {g : Mx k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
    exact isClosed_eq ((hid.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hid)
      continuous_const
  let f : C(Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ℂ) :=
    ⟨fun g => ⟪v, σ g x⟫_ℂ, (continuousOn_const.inner hcont).restrict⟩
  haveI : NormalSpace (Mx k r) :=
    inferInstanceAs (NormalSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hcl f
  exact ⟨⇑G, G.continuous, fun g hg => DFunLike.congr_fun hG ⟨g, hg⟩⟩
end Formalism.FourierDecayAlt.P.S3dx4
