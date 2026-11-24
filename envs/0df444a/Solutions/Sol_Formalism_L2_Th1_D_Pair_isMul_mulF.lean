-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.isMul_mulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:26.429304+00:00
-- url     : https://prove2.me/submissions/aab5b939-1361-488b-b7b8-a7b9cc63e24c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_ps
import Theorems.Thm_Formalism_L2_Th1_D_Pair_ps_comp
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_C_mul_lgF

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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.Pair
theorem _root_.solution (hE : ExpSpec) {l : ℕ} (hl : 2 ≤ l) (c : K) : IsMul l c (mulF K l c) := by
  refine ⟨cc_ps (τ := Unit) (cc_C_mul_lgF hl c) (hE K l hl).1, ?_⟩
  have h1 := ps_comp (τ := Unit) (a := PowerSeries.C c * lgF K l) (cc_C_mul_lgF hl c)
    (hE K l hl).1 (lgF K l)
  rw [(hE K l hl).2.1] at h1
  first
  | exact h1.trans (PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (cc_C_mul_lgF hl c)))
  | (unfold mulF; rw [h1]; simp [PowerSeries.subst_X, PowerSeries.HasSubst.of_constantCoeff_zero (cc_C_mul_lgF hl c)])
end Formalism.L2.Th1.D.Pair
