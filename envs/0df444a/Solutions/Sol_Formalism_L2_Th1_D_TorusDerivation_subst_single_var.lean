-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.subst_single_var
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:11.582714+00:00
-- url     : https://prove2.me/submissions/6677c770-de48-4d6f-bda5-25127d4ea006

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
theorem _root_.solution {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b)
    (x : ι) (f : PowerSeries K) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  have h := MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X x :
    PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K)).const hb f
  rw [MvPowerSeries.subst_X hb] at h
  exact h
end Formalism.L2.Th1.D.TorusDerivation
