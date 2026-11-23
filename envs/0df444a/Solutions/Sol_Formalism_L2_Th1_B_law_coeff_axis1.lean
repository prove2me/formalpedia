-- Prove2me | solution 1 for Formalism.L2.Th1.B.law_coeff_axis1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:32.660808+00:00
-- url     : https://prove2.me/submissions/ff5bb2dc-6a2f-4691-98aa-b8c7720b9d53

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective)
variable {K : Type} [Field K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution (H : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) (hn : n 0 = 0) :
    MvPowerSeries.coeff n H = MvPowerSeries.coeff n
      (MvPowerSeries.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] H) := by
  have e : ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] =
      (![0, 1] : Fin 2 → K) • MvPowerSeries.X := by
    funext s
    fin_cases s <;> simp
  rw [e, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_two, hn]
end Formalism.L2.Th1.B
