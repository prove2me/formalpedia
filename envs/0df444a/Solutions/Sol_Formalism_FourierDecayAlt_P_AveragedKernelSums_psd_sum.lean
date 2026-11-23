-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.psd_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:54.741128+00:00
-- url     : https://prove2.me/submissions/e4eac295-4153-430f-8b3e-cf90bad2ad08

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
theorem _root_.solution {X ι : Type} (F : Finset X) (s : Finset ι) (k : ι → X → X → ℂ)
    (h : ∀ i ∈ s, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ s, k i x y) := by
  intro a
  have E : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (∑ i ∈ s, k i x y) =
      ∑ i ∈ s, ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k i x y := by
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
  rw [E, Complex.im_sum, Complex.re_sum]
  exact ⟨Finset.sum_eq_zero fun i hi => (h i hi a).1, Finset.sum_nonneg fun i hi => (h i hi a).2⟩
end Formalism.FourierDecayAlt.P.AveragedKernelSums
