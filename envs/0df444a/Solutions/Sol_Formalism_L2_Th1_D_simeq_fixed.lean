-- Prove2me | solution 1 for Formalism.L2.Th1.D.simeq_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:48:21.226093+00:00
-- url     : https://prove2.me/submissions/77f0ec01-0149-49b3-8131-f8719d5d2fc2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_dworkMv
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
open TraceNormBounds
namespace Formalism.L2.Th1.D
theorem _root_.solution : SimeqFixed := by
  intro K _ _ _ l σ hU τ _ f c hc hfix hs
  obtain ⟨hp, hp2, hpn, hval, hσ⟩ := hU
  obtain ⟨h0, hI⟩ := hs
  rw [sub_zero] at h0 hI
  have hp0 : l ≠ 0 := hp.ne_zero
  have hD := Formalism.InvariantFactorPaths.G7.Top.dworkMv
  have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.C c * f) = 0 := by simp [h0]
  refine ⟨by rwa [sub_zero], ?_⟩
  rw [sub_zero, hD K τ l σ hp hpn hσ _ h0']
  have hcf := (hD K τ l σ hp hpn hσ f h0).1 hI
  intro n
  have he : frobVar l (MvPowerSeries.map σ (MvPowerSeries.C c * f)) -
      MvPowerSeries.C (l : K) * (MvPowerSeries.C c * f) =
      MvPowerSeries.C c * (frobVar l (MvPowerSeries.map σ f) - MvPowerSeries.C (l : K) * f) := by
    rw [map_mul, MvPowerSeries.map_C, hfix, Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hp0,
      Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hp0, map_mul, MvPowerSeries.expand_C]
    ring
  rw [he, MvPowerSeries.coeff_C_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hcf n)
end Formalism.L2.Th1.D
