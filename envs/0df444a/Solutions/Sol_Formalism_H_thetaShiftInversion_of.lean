-- Prove2me | solution 1 for Formalism.H.thetaShiftInversion_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:54.038603+00:00
-- url     : https://prove2.me/submissions/e4e81f2f-8707-42df-b110-c750ae8c013d

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution (hP : PoissonDecay V) (h2 : Periodization V) (h5 : GaussFourier V) :
    ThetaShiftInversion V := by
  intro Λ _ _ t ht x
  obtain ⟨hc, hO, hF⟩ := h5 t ht
  have hd : (Module.finrank ℝ V : ℝ) < Module.finrank ℝ V + 1 := by linarith
  obtain ⟨hsum, hhas⟩ := hP Λ _ hc _ hd (hO _) (by
    have hO2 := (hO (Module.finrank ℝ V + 1))

    have hfun : (𝓕 (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) : V → ℂ) =
        fun w => ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) * (Real.exp (-Real.pi * ‖w‖ ^ 2 / t) : ℂ) :=
      funext hF
    obtain ⟨-, hO', -⟩ := h5 (1 / t) (by positivity)
    rw [hfun]
    refine ((hO' (Module.finrank ℝ V + 1)).congr_left fun w => ?_).const_mul_left _
    congr 2
    field_simp) x
  simp only [hF] at hsum hhas
  set c : ℂ := ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ)
  have hc0 : c ≠ 0 := by
    simp only [c, ne_eq, Complex.ofReal_eq_zero]; exact (Real.rpow_pos_of_pos ht _).ne'
  have hsum' : Summable (fun μ : dual Λ => (Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) := by
    refine (hsum.mul_left c⁻¹).congr fun μ => ?_
    field_simp
  refine ⟨hsum', ?_⟩
  rw [thetaShift, Complex.ofReal_tsum, hhas.tsum_eq]
  have : (fun μ : dual Λ => c * (Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) =
      fun μ : dual Λ => c * ((Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) := by
    funext μ; ring
  rw [this, tsum_mul_left]
  ring
end Formalism.H
