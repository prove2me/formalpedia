-- Prove2me | solution 1 for Formalism.L2.Th1.D.SubstitutionCoefficientLemmas.coeff_subst_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:11:45.720881+00:00
-- url     : https://prove2.me/submissions/83e26b6e-bc94-40ec-9e6d-2f1c4d54fd8a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IntegralPartAtVariable

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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
open Pair InverseCommuting
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
theorem _root_.solution {ι τ : Type} {a : ι → MvPowerSeries τ K} (ha : HasSubst a) (e : τ →₀ ℕ) :
    ∃ T : Finset (ι →₀ ℕ), ∀ g : MvPowerSeries ι K,
      coeff e (subst a g) = ∑ d ∈ T, coeff d g * coeff e (d.prod fun s k => a s ^ k) := by
  let u : MvPowerSeries ι K := fun _ => 1
  have hu : ∀ d, coeff d u = 1 := fun d => coeff_apply u d
  have hfin : (Function.support
      fun d => coeff d u • coeff e (d.prod fun s k => a s ^ k)).Finite :=
    coeff_subst_finite ha u e
  refine ⟨hfin.toFinset, fun g => ?_⟩
  rw [coeff_subst ha, finsum_eq_sum_of_support_subset]
  · rfl
  · intro d hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    rw [Function.mem_support] at hd
    intro h0
    apply hd
    rw [hu, one_smul] at h0
    rw [h0, smul_zero]
end Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
