-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.subst_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:41.962873+00:00
-- url     : https://prove2.me/submissions/bcc176ed-b194-4fc7-8cd2-2c5f576641cf

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
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.TorusDerivation
theorem _root_.solution {σ' τ : Type} {a : σ' → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (0 : MvPowerSeries σ' K) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_zero]
end Formalism.L2.Th1.D.TorusDerivation
