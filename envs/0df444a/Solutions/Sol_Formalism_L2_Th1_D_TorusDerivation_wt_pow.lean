-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.wt_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:42.777422+00:00
-- url     : https://prove2.me/submissions/c6a298c3-7aa7-41ac-a39c-ee2f1f5ea048

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
theorem _root_.solution {l N : ℕ} {ζ : K} (h : ζ ^ N = 1) (n : ZMod d →₀ ℕ) : wt l ζ n ^ N = 1 := by
  unfold wt
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun s _ => ?_
  have e : (ζ ^ lw l s) ^ N = 1 := by
    rw [← zpow_natCast (ζ ^ lw l s) N, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]
  rw [← pow_mul, mul_comm, pow_mul, e, one_pow]
end Formalism.L2.Th1.D.TorusDerivation
