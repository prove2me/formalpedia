-- Prove2me | solution 1 for Formalism.H.thetaInversion_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:53.599791+00:00
-- url     : https://prove2.me/submissions/9379f920-6a41-4acf-9d78-1fd5a68c5c27

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
theorem _root_.solution (hS : ThetaShiftInversion V) : ThetaInversion V := by
  intro Λ _ _ t ht
  obtain ⟨-, h⟩ := hS Λ (1 / t) (by positivity) 0
  have hl : thetaShift Λ (1 / t) 0 = theta Λ (1 / t) := by
    simp [thetaShift, theta]
  rw [hl] at h
  have hr : ∀ μ : dual Λ, (Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / (1 / t)) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), (0 : V)⟫ : ℝ)) =
      ((Real.exp (-Real.pi * t * ‖(μ : V)‖ ^ 2) : ℝ) : ℂ) := by
    intro μ
    rw [inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    congr 2
    field_simp
  simp only [hr] at h
  rw [← Complex.ofReal_tsum] at h
  have hpow : (1 / t) ^ (-(Module.finrank ℝ V : ℝ) / 2) = t ^ ((Module.finrank ℝ V : ℝ) / 2) := by
    rw [one_div, Real.inv_rpow ht.le, neg_div, Real.rpow_neg ht.le, inv_inv]
  rw [hpow] at h
  have h' : (theta Λ (1 / t) : ℂ) = (((ZLattice.covolume Λ)⁻¹ * t ^ ((Module.finrank ℝ V : ℝ) / 2) *
      theta (dual Λ) t : ℝ) : ℂ) := by
    rw [h, theta]; push_cast; ring
  exact_mod_cast h'
end Formalism.H
