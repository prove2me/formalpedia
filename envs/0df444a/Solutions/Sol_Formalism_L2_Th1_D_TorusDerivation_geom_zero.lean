-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.geom_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:18.456365+00:00
-- url     : https://prove2.me/submissions/de8ae71c-c3fe-44a3-a416-7bd8cfe9bcd7

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
theorem _root_.solution {w : K} {N : ℕ} (h : w ^ N = 1) (h1 : w ≠ 1) :
    ∑ k ∈ Finset.range N, w ^ k = 0 := by
  have h2 := mul_geom_sum w N
  rw [h, sub_self] at h2
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 h1)
end Formalism.L2.Th1.D.TorusDerivation
