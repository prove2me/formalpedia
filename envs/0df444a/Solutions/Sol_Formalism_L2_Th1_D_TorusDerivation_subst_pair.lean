-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.subst_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:33.779998+00:00
-- url     : https://prove2.me/submissions/afb761bc-6517-49e2-a955-8b04b3820c48

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_hasSubst_pair

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
theorem _root_.solution {τ κ : Type} {A B : MvPowerSeries τ K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0)
    {b : τ → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b) (G : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.subst b (MvPowerSeries.subst ![A, B] G) =
      MvPowerSeries.subst ![MvPowerSeries.subst b A, MvPowerSeries.subst b B] G := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pair hA hB) hb]
  congr 1
  funext i
  fin_cases i <;> simp
end Formalism.L2.Th1.D.TorusDerivation
