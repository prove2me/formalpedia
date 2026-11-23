-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.psubst_fExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:12.290242+00:00
-- url     : https://prove2.me/submissions/ffdd37b2-b255-465b-821e-7cb4b5668801

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParO
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.ParO
theorem _root_.solution {ι : Type} {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst u (fExp f) = fExp (PowerSeries.subst u f) := by
  simp only [Formalism.L2.Th1.B.fExp]
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hf)
    (PowerSeries.HasSubst.of_constantCoeff_zero hu) _
end Formalism.L2.Th1.B.ParO
