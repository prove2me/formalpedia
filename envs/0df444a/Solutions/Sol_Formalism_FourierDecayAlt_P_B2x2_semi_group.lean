-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.semi_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:01:28.713742+00:00
-- url     : https://prove2.me/submissions/38e84708-671e-4954-9912-7af1109176c6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution {k r : ℕ} (A B : Set (Mat k r)) (hA : IsClosedSubgroup A) (hB : IsClosedSubgroup B)
    (hn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hcl : IsClosed (mulSet A B)) : IsClosedSubgroup (mulSet A B) := by
  refine ⟨⟨1, hA.one_mem, 1, hB.one_mem, (mul_one 1).symm⟩, ?_, ?_, ?_, hcl⟩
  · rintro _ ⟨a1, ha1, b1, hb1, rfl⟩ _ ⟨a2, ha2, b2, hb2, rfl⟩
    have hu : IsUnit b1.det := hB.unit b1 hb1
    refine ⟨a1 * (b1 * a2 * b1⁻¹), hA.mul_mem _ ha1 _ (hn b1 hb1 a2 ha2), b1 * b2,
      hB.mul_mem _ hb1 _ hb2, ?_⟩
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    have hu : IsUnit b.det := hB.unit b hb
    have hbi : b⁻¹ ∈ B := hB.inv_mem b hb
    refine ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, hn _ hbi _ (hA.inv_mem a ha), b⁻¹, hbi, ?_⟩
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv b hu,
      Matrix.mul_assoc (b⁻¹ * a⁻¹) b b⁻¹, Matrix.mul_nonsing_inv b hu, Matrix.mul_one]
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [Matrix.det_mul]
    exact (hA.unit a ha).mul (hB.unit b hb)
end Formalism.FourierDecayAlt.P.B2x2
