-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.law_left_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:11.477811+00:00
-- url     : https://prove2.me/submissions/2bb70b84-72ea-4f8f-ba33-71d563a6320d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs2
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_lgF
import Theorems.Thm_Formalism_L2_Th1_D_Pair_exp_log
import Theorems.Thm_Formalism_L2_Th1_D_Pair_hs2
import Theorems.Thm_Formalism_L2_Th1_D_Pair_log_law
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_zero_of_constantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_expSpec


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) {F : MvPowerSeries (Fin 2) K}
    (hF0 : constantCoeff F = 0) (hF : cob F (lgF K l) = 0) {τ : Type} {a : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) : subst ![0, a] F = a := by
  have h := Pair.log_law hF0 hF (map_zero (constantCoeff (σ := τ) (R := K))) ha
  rw [TorusDerivation.subst_zero_of_constantCoeff _ (Pair.cc_lgF hl), zero_add] at h
  have hc : constantCoeff (subst ![0, a] F) = 0 :=
    constantCoeff_subst_eq_zero (Pair.hs2 (map_zero _) ha)
      (by intro i; fin_cases i <;> simp [ha]) hF0
  have h2 := Pair.exp_log expSpec hl hc
  rw [h, Pair.exp_log expSpec hl ha] at h2
  exact h2.symm
end Formalism.L2.Th1.D.TraceNormBounds
