-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:16.920323+00:00
-- url     : https://prove2.me/submissions/86022a66-4f7c-4fc3-b06a-5ede75a2104a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Map
open Formalism.InvariantFactorPaths.G7 (at1 cob)
variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
namespace Formalism.L2.Th1.B.Map
theorem _root_.solution {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    MvPowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (MvPowerSeries.map j a) (PowerSeries.map j f) := by
  have ha' : MvPowerSeries.constantCoeff (MvPowerSeries.map j a) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, ha, map_zero]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero ha'
  ext e
  rw [MvPowerSeries.coeff_map, PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs',
    map_finsum j (PowerSeries.coeff_subst_finite hs f e)]
  refine finsum_congr fun d => ?_
  rw [smul_eq_mul, smul_eq_mul, map_mul, PowerSeries.coeff_map, ← map_pow (MvPowerSeries.map j),
    MvPowerSeries.coeff_map]
end Formalism.L2.Th1.B.Map
