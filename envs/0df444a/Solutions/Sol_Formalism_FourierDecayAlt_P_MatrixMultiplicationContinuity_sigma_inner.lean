-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:17.279409+00:00
-- url     : https://prove2.me/submissions/52f72660-a609-4509-be2f-66bbd749c800

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_uh_inv
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
    {σ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (v u : H) :
    ⟪v, σ g u⟫_ℂ = ⟪σ g⁻¹ v, u⟫_ℂ := by
  obtain ⟨P, hP, hDS⟩ := id hσ
  obtain ⟨-, -, ⟨⟨h1, hmul⟩, hnorm, -⟩, -⟩ := hDS
  have hPu : IsUnit P := hP.1.1
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  obtain ⟨hgi, hggi, hgig⟩ := uh_inv hg
  have hm1 := cayley_maps hP hg
  have hm2 := cayley_maps hP hgi
  have conj : ∀ x : Formalism.FourierDecayAlt.ThreeDimData.Mx k r, P⁻¹ * (P * x * P⁻¹) * P = x := fun x => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPiP, Matrix.one_mul, Matrix.mul_assoc, hPiP, Matrix.mul_one]
  have prod : ∀ x y : Formalism.FourierDecayAlt.ThreeDimData.Mx k r, (P * x * P⁻¹) * (P * y * P⁻¹) = P * (x * y) * P⁻¹ := fun x y => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, hPiP, Matrix.one_mul]
  have hm := hmul _ hm1 _ hm2
  simp only [prod, hggi, conj, Matrix.mul_one, Matrix.one_mul, hPiP, hPPi] at hm h1

  have hsg : ∀ w, σ g (σ g⁻¹ w) = w := fun w => by
    have := congrArg (fun T : H →L[ℂ] H => T w) hm
    simp only [ContinuousLinearMap.comp_apply, h1, ContinuousLinearMap.one_apply] at this
    exact this.symm
  have hn : ∀ w, ‖σ g w‖ = ‖w‖ := fun w => by
    have := hnorm _ hm1 w
    simp only [conj] at this
    exact this
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hn }
  calc ⟪v, σ g u⟫_ℂ = ⟪L (σ g⁻¹ v), L u⟫_ℂ := by
        show ⟪v, σ g u⟫_ℂ = ⟪σ g (σ g⁻¹ v), σ g u⟫_ℂ
        rw [hsg]
    _ = ⟪σ g⁻¹ v, u⟫_ℂ := L.inner_map_map _ _
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
