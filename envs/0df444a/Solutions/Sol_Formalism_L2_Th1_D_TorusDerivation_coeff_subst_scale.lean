-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.coeff_subst_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:33.048952+00:00
-- url     : https://prove2.me/submissions/9017a892-5ed7-46f1-a3fa-6cfe39cc6354

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
theorem _root_.solution {τ : Type} [Fintype τ] (a : τ → K) (f : MvPowerSeries τ K) (n : τ →₀ ℕ) :
    MvPowerSeries.coeff n
        (MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) f) =
      (∏ s, a s ^ n s) * MvPowerSeries.coeff n f := by
  have ht : (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) =
      a • (MvPowerSeries.X : τ → MvPowerSeries τ K) := by
    funext s
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [ht, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
end Formalism.L2.Th1.D.TorusDerivation
