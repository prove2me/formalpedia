-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.poissonSummable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:21.459797+00:00
-- url     : https://prove2.me/submissions/b1b8996c-36aa-47df-992f-11c77637721d

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_loc_summable_pt
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_loc_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_loc_per
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_loc_integrable
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_H_lattice_fourier_series
import Theorems.Thm_Formalism_H_unfoldCoeff_main
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution : PoissonSummable := by
  intro V _ _ _ _ _ Λ _ _ φ hc hloc hsum x
  have hint := loc_integrable Λ φ hc hloc
  let b := Module.Free.chooseBasis ℤ Λ
  have hD := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hGc : Continuous (fun y : V => ∑' l : Λ, φ ((l : V) + y)) := loc_cont Λ φ hc hloc
  have hGp : ∀ (l : Λ) (y : V), (fun y : V => ∑' l : Λ, φ ((l : V) + y)) ((l : V) + y) =
      (fun y : V => ∑' l : Λ, φ ((l : V) + y)) y := fun l y => loc_per Λ φ l y
  have hcoef : ∀ μ : dual Λ, ∫ y in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ),
      (fun y : V => ∑' l : Λ, φ ((l : V) + y)) y *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ))) = (𝓕 φ : V → ℂ) μ :=
    fun μ => unfoldCoeff_main Λ φ hint _ hD μ μ.2
  have hsumF : Summable (fun μ : dual Λ => (𝓕 φ : V → ℂ) μ) := summable_norm_iff.mp hsum
  have hLFS := lattice_fourier_series V Λ _ hGc hGp _ hD (by simpa only [hcoef] using hsumF) x
  simp only [hcoef] at hLFS
  have hexp : ∀ μ : dual Λ, ‖Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))‖ = 1 := by
    intro μ
    rw [Complex.norm_exp]
    simp
  refine ⟨Summable.of_norm_bounded hsum (fun μ => by rw [norm_mul, hexp, mul_one]), ?_⟩
  have hG : (∑' l : Λ, φ ((l : V) + x)) = (ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ,
      (𝓕 φ : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)) := by
    rw [← hLFS.tsum_eq, ← tsum_mul_left]
    exact tsum_congr fun μ => mul_assoc _ _ _
  rw [← hG]
  exact (loc_summable_pt Λ φ hloc x).hasSum
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
