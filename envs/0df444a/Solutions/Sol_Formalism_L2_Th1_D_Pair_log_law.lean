-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.log_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:04.362918+00:00
-- url     : https://prove2.me/submissions/1c3b0700-6e95-4ba6-9d75-4697b9b882b9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_hs2
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_subst1
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_single_var
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
namespace Pair
section Alg
variable {K : Type} [Field K]
private theorem mvSubst_add {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f g : MvPowerSeries ι K) : subst φ (f + g) = subst φ f + subst φ g := by
  first
  | exact MvPowerSeries.subst_add hφ f g
  | (rw [← coe_substAlgHom hφ]; exact map_add _ f g)
  | exact map_add (substAlgHom hφ) f g
end Alg
section NormedLin
variable {K : Type} [NormedField K]
end NormedLin
section Normed
variable {K : Type} [NormedField K] [CharZero K]
end Normed
end Pair
open Pair
end Formalism.L2.Th1.D
end
end

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
theorem _root_.solution {l : ℕ} {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0)
    (hF : cob F (lgF K l) = 0) {τ : Type} {a b : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    PowerSeries.subst (subst ![a, b] F) (lgF K l) =
      PowerSeries.subst a (lgF K l) + PowerSeries.subst b (lgF K l) := by
  have h2 := hs2 ha hb
  have e : PowerSeries.subst F (lgF K l) = at1 0 (lgF K l) + at1 1 (lgF K l) := by
    unfold cob at hF
    rw [sub_sub, sub_eq_zero] at hF
    exact hF
  have h := congrArg (subst ![a, b]) e
  rw [mvSubst_add h2, subst_subst1 h2 (PowerSeries.HasSubst.of_constantCoeff_zero hF0),
    subst_single_var h2, subst_single_var h2] at h
  exact h
end Formalism.L2.Th1.D.Pair
