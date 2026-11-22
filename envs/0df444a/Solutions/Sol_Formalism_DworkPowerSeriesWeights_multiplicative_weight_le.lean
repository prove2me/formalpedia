-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.multiplicative_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:56.762811+00:00
-- url     : https://prove2.me/submissions/5ebfcaa5-f151-44e7-a384-6f680919bdab

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormNatCastEqOneOfNotDvd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : MulWtLe.{u, v} := by
  intro K _ _ pi h0 ι r w1 w2 κ f g hf hg
  classical
  intro n hn
  rw [monoWtGe_iff, MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
    fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 : x.1 ≤ κ := le_trans (hx ▸ le_self_add) hn
  have h2 : x.2 ≤ κ := le_trans (hx ▸ le_add_self) hn
  rw [norm_mul, ← hx, dot_add]
  calc ‖MvPowerSeries.coeff x.1 f‖ * ‖MvPowerSeries.coeff x.2 g‖
      ≤ pi ^ (w1 - dot x.1 r) * pi ^ (w2 - dot x.2 r) :=
        mul_le_mul (hf x.1 h1) (hg x.2 h2) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = pi ^ (w1 + w2 - (dot x.1 r + dot x.2 r)) := by
        rw [← Real.rpow_add h0]; congr 1; ring
end Formalism.DworkPowerSeriesWeights
