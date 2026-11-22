-- Prove2me | solution 1 for Formalism.QuantumDeterminants.unitary_group_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:44.511296+00:00
-- url     : https://prove2.me/submissions/07e4c0de-0f97-4f3c-9c41-2d90f54e4b2b

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution : UHGroup := by
  intro m H hH
  refine ⟨?_, ?_, ?_⟩
  · show (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * H * 1 = H
    simp
  · intro g hg h' hh
    have hg' : gᴴ * H * g = H := hg
    have hh' : h'ᴴ * H * h' = H := hh
    show (g * h')ᴴ * H * (g * h') = H
    rw [Matrix.conjTranspose_mul]
    calc h'ᴴ * gᴴ * H * (g * h') = h'ᴴ * (gᴴ * H * g) * h' := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [hg', hh']
  · intro g hg
    have hg' : gᴴ * H * g = H := hg
    have hdet : IsUnit g.det := by
      have e := congrArg Matrix.det hg'
      rw [Matrix.det_mul, Matrix.det_mul] at e
      rw [isUnit_iff_ne_zero] at hH ⊢
      intro h0
      rw [h0, mul_zero] at e
      exact hH e.symm
    refine ⟨hdet, ?_⟩
    show (g⁻¹)ᴴ * H * g⁻¹ = H
    have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
    calc (g⁻¹)ᴴ * H * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * H * g) * g⁻¹ := by rw [hg']
      _ = (g * g⁻¹)ᴴ * H * (g * g⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [h1]; simp
end Formalism.QuantumDeterminants
