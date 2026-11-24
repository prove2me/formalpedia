-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:54:08.925792+00:00
-- url     : https://prove2.me/submissions/1678d7bf-c12a-456c-8aad-c0b7fa7f09c1

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
section Groups
variable {k r : ℕ}
private theorem hpk_sq_lemma (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  obtain ⟨s, hs⟩ : ∃ s : Fin (2 * r + k + 1),
      s.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) :=
    ⟨⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩, rfl⟩
  rw [Finset.sum_eq_single s]
  · simp only [Formalism.QuantumDeterminants.Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs ⊢ <;> first | omega | norm_num
  · intro l _ hl
    simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff] at hl ⊢
    split_ifs at hs ⊢ <;> first | omega | simp
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem inv_mem_UH_Hpk_and_mul_inv_of_mem {k r : ℕ} {g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hH : (Formalism.QuantumDeterminants.Hpk k r).det ≠ 0 := by
    intro h0
    have h3 := congrArg Matrix.det (hpk_sq_lemma k r)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h3
    exact zero_ne_one h3
  have hdet : IsUnit g.det := by
    have h3 := congrArg Matrix.det hg'
    rw [Matrix.det_mul, Matrix.det_mul] at h3
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h3
    exact hH h3.symm
  have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  have h2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  refine ⟨?_, h1, h2⟩
  show (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = Formalism.QuantumDeterminants.Hpk k r
  calc (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * g⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
end Groups
section Pi
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
end Pi
section Sigma
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end Sigma
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
end
end

set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
theorem _root_.solution {g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  exact inv_mem_UH_Hpk_and_mul_inv_of_mem hg
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
