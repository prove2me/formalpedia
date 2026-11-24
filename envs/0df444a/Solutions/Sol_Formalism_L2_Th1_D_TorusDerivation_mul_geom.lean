-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.mul_geom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:04.768226+00:00
-- url     : https://prove2.me/submissions/2137c6ff-8fbd-4413-ba7d-61b3a6f2e892

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (torus lw degE degO NoLowBidegree)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB)
open TorusDerivation
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.TorusDerivation
theorem _root_.solution {w : K} {N : ℕ} (h : w ^ N = 1) :
    w * ∑ k ∈ Finset.range N, w ^ k = ∑ k ∈ Finset.range N, w ^ k := by
  have h1 := Finset.sum_range_succ (fun k => w ^ k) N
  have h2 := Finset.sum_range_succ' (fun k => w ^ k) N
  have h3 := h2.symm.trans h1
  rw [h, pow_zero] at h3
  rw [Finset.mul_sum, ← add_right_cancel h3]
  exact Finset.sum_congr rfl fun k _ => (pow_succ' w k).symm
end Formalism.L2.Th1.D.TorusDerivation
