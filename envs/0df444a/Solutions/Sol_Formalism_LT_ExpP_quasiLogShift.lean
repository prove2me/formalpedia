-- Prove2me | solution 1 for Formalism.LT.ExpP.quasiLogShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:56.073163+00:00
-- url     : https://prove2.me/submissions/f8a3f177-3795-474e-bf6f-145564957cf6

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Theorems.Thm_Formalism_LT_ExpP_norm_finsum_le
import Theorems.Thm_Formalism_LT_ExpP_term_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.ExpP
theorem _root_.solution : Formalism.LT.QuasiLogShift.{u} := by
  intro K _ _ p hp hp1 z hz0 hdz e
  have ha : PowerSeries.HasSubst
      (MvPowerSeries.X (0 : Fin 2) + (p : K) • MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hb : PowerSeries.HasSubst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X 0
  unfold Formalism.G.atX
  rw [map_sub, PowerSeries.coeff_subst ha, PowerSeries.coeff_subst hb,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite ha z e) (PowerSeries.coeff_subst_finite hb z e)]
  refine norm_finsum_le (norm_nonneg _) fun d => ?_
  rw [← smul_sub, ← map_sub]
  exact term_bound hp hp1 z hdz d e
end Formalism.LT.ExpP
