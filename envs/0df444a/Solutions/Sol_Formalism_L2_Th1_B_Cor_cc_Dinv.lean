-- Prove2me | solution 1 for Formalism.L2.Th1.B.Cor.cc_Dinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:30:06.802083+00:00
-- url     : https://prove2.me/submissions/220eff5a-bc39-49ec-a744-19faa61c12d9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_SigmaOneCocycleShifted
import Theorems.Thm_Formalism_L2_Th1_B_Jets_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Cor
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
namespace Formalism.L2.Th1.B.Cor
theorem _root_.solution {K : Type} [Field K] [CharZero K] (l f : PowerSeries K)
    (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.constantCoeff (Dinv l f) = PowerSeries.coeff 1 f := by
  have key : ∀ g : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.derivative K g) =
      PowerSeries.coeff 1 g := by
    intro g
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  unfold Dinv
  rw [map_mul, PowerSeries.constantCoeff_inv, key, key, h1, inv_one, one_mul]
end Formalism.L2.Th1.B.Cor
