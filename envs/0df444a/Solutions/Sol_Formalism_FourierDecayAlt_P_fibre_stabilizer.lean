-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.fibre_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:42:04.255999+00:00
-- url     : https://prove2.me/submissions/268c9702-d56d-4f9a-a540-1fb99757308d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Theorems.Thm_Formalism_FourierDecayAlt_P_fixed_frame_property
import Theorems.Thm_Formalism_FourierDecayAlt_P_majorant_estimate
import Theorems.Thm_Formalism_QuantumDeterminants_uHGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.FibreStab := by
  intro k r z z' hstd g hg _
  have hHdet : IsUnit (Hpk k r).det :=
    Matrix.isUnit_det_of_right_inverse (majorant_estimate k r).2.1
  obtain ⟨_, hmul, hinv⟩ := uHGroup _ (Hpk k r) hHdet
  have hgu : IsUnit g.det := (hinv g hg).1
  have hFz := fixed_frame_property k r z hstd.2.1
  have hFz' := fixed_frame_property k r z' hstd.2.2
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hq, hpq⟩
    rw [← hFz] at hp
    have hpu : IsUnit p.det := (hinv p hp.1).1
    have h1 : g * q = p * g := by
      calc g * q = p * (p⁻¹ * g * q) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hpu, Matrix.one_mul]
        _ = p * g := by rw [hpq]
    have hq_eq : g⁻¹ * p * g = q := by
      calc g⁻¹ * p * g = g⁻¹ * (g * q) := by rw [h1, Matrix.mul_assoc]
        _ = q := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul]
    refine ⟨p, ⟨hp.1, ?_⟩, rfl, hq_eq⟩
    rintro (a | b)
    · exact hp.2 a
    · rw [← hFz'] at hq
      show p *ᵥ (g *ᵥ fvec k r z' b) = g *ᵥ fvec k r z' b
      rw [Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, hq.2 b]
  · rintro ⟨h, ⟨hhV, hhfix⟩, rfl, rfl⟩
    have hhu : IsUnit h.det := (hinv h hhV).1
    refine ⟨?_, ?_, ?_⟩
    · rw [← hFz]
      exact ⟨hhV, fun a => hhfix (Sum.inl a)⟩
    · rw [← hFz']
      refine ⟨hmul _ (hmul _ (hinv g hg).2 h hhV) g hg, fun b => ?_⟩
      have hb : h *ᵥ (g *ᵥ fvec k r z' b) = g *ᵥ fvec k r z' b := hhfix (Sum.inr b)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hgu, Matrix.one_mulVec]
    · calc h⁻¹ * g * (g⁻¹ * h * g) = h⁻¹ * (g * g⁻¹) * h * g := by simp only [Matrix.mul_assoc]
        _ = g := by
          rw [Matrix.mul_nonsing_inv _ hgu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul]
end Formalism.FourierDecayAlt.P
