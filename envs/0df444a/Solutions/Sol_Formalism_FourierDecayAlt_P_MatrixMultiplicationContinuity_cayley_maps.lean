-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:52:40.044965+00:00
-- url     : https://prove2.me/submissions/717334d9-3682-4478-8808-7a5f746945cc

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
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
theorem _root_.solution {ε : Fin (2 * r + k + 1) → Bool} {P : Formalism.FourierDecayAlt.ThreeDimData.Mx k r}
    (hP : PI.UpqRep.IsCayleyU k r ε P) :
    Set.MapsTo (fun g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r => P * g * P⁻¹) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
      (PI.UpqRep.UJset ε) := by
  obtain ⟨⟨hPu, hPJ⟩, -⟩ := hP
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  intro g hg
  have hg' : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹) = PI.UpqRep.Jm ε
  calc (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * P⁻¹ := by rw [hPJ, hg']
    _ = (P * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = PI.UpqRep.Jm ε := by rw [hPPi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
