-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.divAB_of_axes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:17.007807+00:00
-- url     : https://prove2.me/submissions/6558f6b3-6f2b-475a-9766-23787d7751b0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_coeff_subst_scale

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
theorem _root_.solution {H : MvPowerSeries (Fin 2) K}
    (h1 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H = 0)
    (h0 : MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H = 0) :
    DivAB H := by
  intro n hn
  rcases hn with hn | hn
  · have e : (fun s : Fin 2 => MvPowerSeries.C ((![0, 1] : Fin 2 → K) s) * MvPowerSeries.X s) =
        ![(0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] := by
      funext i
      fin_cases i <;> simp
    have := coeff_subst_scale (![0, 1] : Fin 2 → K) H n
    rw [e, h0, Fin.prod_univ_two] at this
    simpa [hn] using this.symm
  · have e : (fun s : Fin 2 => MvPowerSeries.C ((![1, 0] : Fin 2 → K) s) * MvPowerSeries.X s) =
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] := by
      funext i
      fin_cases i <;> simp
    have := coeff_subst_scale (![1, 0] : Fin 2 → K) H n
    rw [e, h1, Fin.prod_univ_two] at this
    simpa [hn] using this.symm
end Formalism.L2.Th1.D.TorusDerivation
