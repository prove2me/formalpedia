-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:14:27.065586+00:00
-- url     : https://prove2.me/submissions/e10b6d16-dd61-4da4-8c7d-e0e0ee61ada9

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_cayley_maps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
theorem _root_.solution {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) :
    σ 1 = 1 ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ v, ‖σ g v‖ = ‖v‖ := by
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨-, -, ⟨⟨h1, -⟩, hnorm, -⟩, -⟩ := hDS
  have hPu : IsUnit P := hP.1.1
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  refine ⟨?_, fun g hg v => ?_⟩
  · simp only [Matrix.mul_one, hPiP] at h1
    exact h1
  · have hmem := cayley_maps hP hg
    have hv := hnorm _ hmem v
    have e : P⁻¹ * (P * g * P⁻¹) * P = g := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPiP, Matrix.one_mul, Matrix.mul_assoc, hPiP, Matrix.mul_one]
    simp only [e] at hv
    exact hv
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
