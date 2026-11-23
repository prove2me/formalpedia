-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.psd_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:54.60363+00:00
-- url     : https://prove2.me/submissions/00a1adb0-9355-4716-a354-d0a54e46626f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.AveragedKernelSums
theorem _root_.solution {X : Type} (F : Finset X) (k : X → X → ℂ) (c : ℝ) (hc : 0 ≤ c) (h : IsPSD F k) :
    IsPSD F (fun x y => (c : ℂ) * k x y) := by
  intro a
  have E : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c : ℂ) * k x y) =
      (c : ℂ) * ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [E]
  obtain ⟨h1, h2⟩ := h a
  constructor
  · rw [Complex.im_ofReal_mul, h1, mul_zero]
  · rw [Complex.re_ofReal_mul]; exact mul_nonneg hc h2
end Formalism.FourierDecayAlt.P.AveragedKernelSums
