-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.lemma_R_core_log_loss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:37.912636+00:00
-- url     : https://prove2.me/submissions/d1b290ed-3411-4e4d-af98-3fbd6946d963

import Definitions.Def_Formalism_GaussJetBounds_StatementO
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbits
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitsLogLoss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_coreL_dot_fintype
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_exponential_weight_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_factValA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_multiplicative_weight_le
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : RCoreA.{u, v} := by
  intro K _ _ _ l hl hpi ι _ sig κ a ha hκa B U hB0 hB hU
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have hrg : gam l = 1 / ((l : ℝ) - 1) - rho l := by
    have ha : (l : ℝ) - 1 ≠ 0 := by linarith
    have hb : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    unfold gam rho
    field_simp
    ring
  have hExp := exponential_weight_le K l hl hpi ι (fun i => rho l + sig i) κ B hB0 hB
  have hk := multiplicative_weight_le K ‖(l : K)‖ h0 ι (fun i => rho l + sig i) 0 0 κ U (mvExp B) hU hExp
    κ le_rfl
  rw [monoWtGe_iff] at hk
  have hf := factValA (K := K) hl hpi κ ha hκa
  rw [norm_mul]
  calc _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
          (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) *
        ‖(l : K)‖ ^ (0 + 0 - dot κ (fun i => rho l + sig i)) :=
        mul_le_mul hf hk (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = _ := by
      rw [← Real.rpow_add h0]
      congr 1
      rw [coreL_dot_fintype, hrg]
      have key : ∑ i, (κ i : ℝ) * (1 / ((l : ℝ) - 1) - rho l - sig i) =
          (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * (rho l + sig i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith
end Formalism.DworkPowerSeriesWeights
