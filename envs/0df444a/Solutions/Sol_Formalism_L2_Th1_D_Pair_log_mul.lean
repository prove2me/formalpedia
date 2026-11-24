-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.log_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:00:14.038143+00:00
-- url     : https://prove2.me/submissions/8e8e9644-c5f8-49f3-b860-1faef767871c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_ps_comp
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
private theorem powerSeries_subst_C_mul {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (c : K) (f : PowerSeries K) :
    PowerSeries.subst a (PowerSeries.C c * f) = C c * PowerSeries.subst a f := by
  have h := PowerSeries.HasSubst.of_constantCoeff_zero ha
  first
  | (simp only [← PowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul]; exact PowerSeries.subst_smul h c f)
  | (rw [PowerSeries.subst_mul h]; congr 1; simp [PowerSeries.subst_C h])
  | (rw [← PowerSeries.coe_substAlgHom h, map_mul]; congr 1; exact (PowerSeries.substAlgHom h).commutes c)
  | simp [PowerSeries.subst_mul h]
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
theorem _root_.solution {l : ℕ} {c : K} {e : PowerSeries K} (he : IsMul l c e) {τ : Type}
    {a : MvPowerSeries τ K} (ha : constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a e) (lgF K l) =
      C c * PowerSeries.subst a (lgF K l) := by
  rw [ps_comp ha he.1 (lgF K l), he.2]
  exact powerSeries_subst_C_mul ha c (lgF K l)
end Formalism.L2.Th1.D.Pair
