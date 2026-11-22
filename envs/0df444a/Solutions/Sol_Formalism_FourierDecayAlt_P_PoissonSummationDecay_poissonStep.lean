-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.poissonStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:27.279082+00:00
-- url     : https://prove2.me/submissions/08dd087e-3ad4-4743-bd67-cfe40f0e6711

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution : PoissonStep := by
  intro V _ _ _ _ _ Λ _ _ φ x hPA hnn S
  obtain ⟨hs, hsum⟩ := hPA
  have hre := Complex.hasSum_re hsum
  have h1 := sum_le_hasSum S (fun l _ => by simpa using hnn l) hre
  simp only [Complex.ofReal_re] at h1
  refine h1.trans ?_
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]
  unfold poissonBound
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (ZLattice.covolume_pos Λ volume).le)
  have hexp : ∀ μ : dual Λ, ‖Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))‖ = 1 := by
    intro μ
    rw [Complex.norm_exp]
    simp
  set a : dual Λ → ℂ := fun μ => (𝓕 (fun v => (φ v : ℂ)) : V → ℂ) μ *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)) with ha
  have hsn := summable_norm_iff.mpr hs
  rw [← Summable.tsum_add_tsum_compl (s := ({0} : Set (dual Λ))) (hs.subtype _) (hs.subtype _), tsum_singleton,
    Complex.add_re]
  have h0 : a 0 = (𝓕 (fun v => (φ v : ℂ)) : V → ℂ) 0 := by
    simp [ha]
  rw [h0]
  gcongr
  refine (Complex.re_le_norm _).trans ((norm_tsum_le_tsum_norm (hsn.subtype _)).trans (le_of_eq ?_))
  refine tsum_congr fun μ => ?_
  simp only [ha]
  rw [norm_mul, hexp, mul_one]
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
