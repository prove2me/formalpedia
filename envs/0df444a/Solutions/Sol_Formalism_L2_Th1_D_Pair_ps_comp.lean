-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.ps_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:39:04.212854+00:00
-- url     : https://prove2.me/submissions/3a3a794b-3872-463e-900c-6f4fa27a5546

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_subst1
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
private theorem hasSubst_finite_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
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
theorem _root_.solution {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0) {e : PowerSeries K}
    (he : PowerSeries.constantCoeff e = 0) (f : PowerSeries K) :
    PowerSeries.subst (PowerSeries.subst a e) f = PowerSeries.subst a (PowerSeries.subst e f) := by
  have h1 : HasSubst (fun _ : Unit => a) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => ha
  exact (subst_subst1 h1 (PowerSeries.HasSubst.of_constantCoeff_zero he) f).symm
end Formalism.L2.Th1.D.Pair
