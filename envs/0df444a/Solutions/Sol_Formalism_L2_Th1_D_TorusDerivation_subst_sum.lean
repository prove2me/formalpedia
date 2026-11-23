-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.subst_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:54.730516+00:00
-- url     : https://prove2.me/submissions/4c86bcd3-f983-4633-9901-f4176d000005

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
theorem _root_.solution {σ' τ α : Type} {a : σ' → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (S : Finset α) (F : α → MvPowerSeries σ' K) :
    MvPowerSeries.subst a (∑ i ∈ S, F i) = ∑ i ∈ S, MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
end Formalism.L2.Th1.D.TorusDerivation
