-- Prove2me | solution 1 for DimdPolyLEAN.symplecticFourierRep_sub_le_lpNorm_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:57.248986+00:00
-- url     : https://prove2.me/submissions/56b54949-34a2-4211-bd88-8302622cc700

module
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Theorems.Thm_DimdPolyLEAN_symplecticFourierPhase_norm

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {d : Nat}
    {G₁ G₂ : PhaseSpace d -> ℂ}
    (h1 : Integrable G₁ (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (h2 : Integrable G₂ (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (ξ : PhaseSpace d) :
    ‖symplecticFourierRep G₁ ξ - symplecticFourierRep G₂ ξ‖ ≤
      MeasureTheory.lpNorm (fun η : PhaseSpace d => G₁ η - G₂ η) 1
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  let μ : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  let φ : PhaseSpace d -> ℂ := fun η =>
    Complex.exp
      ((2 * Real.pi : ℂ) * Complex.I *
        (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))
  have hφ_meas : AEStronglyMeasurable φ μ := (by fun_prop : Measurable φ).aestronglyMeasurable
  have hφ_bound : ∀ᵐ η : PhaseSpace d ∂μ, ‖φ η‖ ≤ (1 : ℝ) := by
    filter_upwards [Filter.Eventually.of_forall
      (fun η : PhaseSpace d => symplecticFourierPhase_norm η ξ)] with η hη
    exact le_of_eq hη
  have hdiff : Integrable (fun η : PhaseSpace d => G₁ η - G₂ η) μ := by exact h1.sub h2
  have h1φ : Integrable (fun η : PhaseSpace d => G₁ η * φ η) μ := h1.mul_bdd hφ_meas hφ_bound
  have h2φ : Integrable (fun η : PhaseSpace d => G₂ η * φ η) μ := h2.mul_bdd hφ_meas hφ_bound
  calc
    ‖symplecticFourierRep G₁ ξ - symplecticFourierRep G₂ ξ‖
        = ‖∫ η : PhaseSpace d, (G₁ η - G₂ η) * φ η ∂μ‖ := by
            unfold symplecticFourierRep
            rw [← MeasureTheory.integral_sub h1φ h2φ]
            have hfun :
                (fun η : PhaseSpace d => G₁ η * φ η - G₂ η * φ η) =
                  (fun η : PhaseSpace d => (G₁ η - G₂ η) * φ η) := by
              funext η
              simp [sub_mul]
            rw [hfun]
    _ ≤ ∫ η : PhaseSpace d, ‖(G₁ η - G₂ η) * φ η‖ ∂μ := by exact norm_integral_le_integral_norm _
    _ = ∫ η : PhaseSpace d, ‖G₁ η - G₂ η‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [Filter.Eventually.of_forall
            (fun η : PhaseSpace d => symplecticFourierPhase_norm η ξ)] with η hη
          rw [norm_mul, hη, mul_one]
    _ = MeasureTheory.lpNorm (fun η : PhaseSpace d => G₁ η - G₂ η) 1 μ := by
          symm
          exact MeasureTheory.lpNorm_one_eq_integral_norm hdiff.aestronglyMeasurable
end DimdPolyLEAN
