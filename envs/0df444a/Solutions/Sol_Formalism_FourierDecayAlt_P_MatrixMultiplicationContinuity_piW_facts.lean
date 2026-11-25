-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:20:50.246578+00:00
-- url     : https://prove2.me/submissions/fbb2a19c-1c1e-415c-9654-1608c6003fbb

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_uwset_eq
import Theorems.Thm_P2M_PI_HwUniqW_inv_mul_UH__9fc24965c5a2
import Theorems.Thm_PI_HwUniqW_UW_eq_conj
import Theorems.Thm_PI_HwUniqW_blockW_mul
import Theorems.Thm_PI_HwUniqW_blockW_one
import Theorems.Thm_PI_HwUniqW_conj_UH
import Theorems.Thm_PI_HwUniqW_conj_fix
import Theorems.Thm_PI_HwUniqW_fix_block
import Theorems.Thm_PI_HwUniqW_mul_inv_UH


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
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) :
    π 1 = 1 ∧ (∀ a ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ b ∈ Formalism.QuantumDeterminants.UWset k r z, π (a * b) = (π a).comp (π b)) ∧
      (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ w, ‖π h w‖ = ‖w‖) ∧
      (∀ w, ContinuousOn (fun h => π h w) (Formalism.QuantumDeterminants.UWset k r z)) := by
  rw [uwset_eq]
  obtain ⟨g, hg, hρ⟩ := hπ
  obtain ⟨⟨h1, hmul⟩, hunit, hcont⟩ := hρ.2.2.1
  have hgg : g * g⁻¹ = 1 := PI.HwUniqW.mul_inv_UH hg.1
  have hgg' : g⁻¹ * g = 1 := PI.HwUniqW.inv_mul_UH' hg.1
  have hT' : 0 < PI.UpqRep.Tz k r z := hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) = g * PI.UpqRep.blockW k r 1 * g⁻¹ := by
      rw [PI.HwUniqW.blockW_one, Matrix.mul_one, hgg]
    rw [e]; exact h1
  · intro a ha b hb
    obtain ⟨x, hx, -, rfl⟩ := PI.HwUniqW.UW_eq_conj hT' hg ha
    obtain ⟨y, hy, -, rfl⟩ := PI.HwUniqW.UW_eq_conj hT' hg hb
    have e : g * PI.UpqRep.blockW k r x * g⁻¹ * (g * PI.UpqRep.blockW k r y * g⁻¹) =
        g * PI.UpqRep.blockW k r (x * y) * g⁻¹ := by
      rw [← PI.HwUniqW.blockW_mul]
      calc g * PI.UpqRep.blockW k r x * g⁻¹ * (g * PI.UpqRep.blockW k r y * g⁻¹)
          = g * PI.UpqRep.blockW k r x * (g⁻¹ * g) * PI.UpqRep.blockW k r y * g⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgg', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e]; exact hmul x hx y hy
  · intro h hh w
    obtain ⟨x, hx, -, rfl⟩ := PI.HwUniqW.UW_eq_conj hT' hg hh
    exact hunit x hx w
  · intro w
    have hc : Continuous (fun h : Formalism.FourierDecayAlt.ThreeDimData.Mx k r => PI.HwUniqW.sub k r (g⁻¹ * h * g)) := by
      have h0 : Continuous (fun h : Formalism.FourierDecayAlt.ThreeDimData.Mx k r => g⁻¹ * h * g) :=
        (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      unfold PI.HwUniqW.sub
      exact continuous_pi fun a => continuous_pi fun b =>
        (continuous_apply_apply (PI.HwUniqW.bl k r a) (PI.HwUniqW.bl k r b)).comp h0
    have hmaps : Set.MapsTo (fun h : Formalism.FourierDecayAlt.ThreeDimData.Mx k r => PI.HwUniqW.sub k r (g⁻¹ * h * g))
        (PI.UpqRep.UWset k r z) (PI.UpqRep.UJset (PI.UpqRep.allPos k)) := fun h hh =>
      (PI.HwUniqW.fix_block (PI.HwUniqW.conj_UH hg hh) (PI.HwUniqW.conj_fix hT' hg hh)).1
    refine ((hcont w).comp hc.continuousOn hmaps).congr ?_
    intro h hh
    have hb := (PI.HwUniqW.fix_block (PI.HwUniqW.conj_UH hg hh) (PI.HwUniqW.conj_fix hT' hg hh)).2
    show π h w = π (g * PI.UpqRep.blockW k r (PI.HwUniqW.sub k r (g⁻¹ * h * g)) * g⁻¹) w
    rw [← hb]
    congr 2
    calc h = (g * g⁻¹) * h * (g * g⁻¹) := by rw [hgg, Matrix.one_mul, Matrix.mul_one]
      _ = g * (g⁻¹ * h * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
