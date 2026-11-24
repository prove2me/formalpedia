-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.coeff_one_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:36:41.606459+00:00
-- url     : https://prove2.me/submissions/dc6a58a2-82f0-4b40-9841-33d390a8e4e2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_FG_InjVAux_Good_pow
import Theorems.Thm_Formalism_FG_InjVAux_eq_single_of_degree_eq_one
import Theorems.Thm_Formalism_FG_InjVAux_good_prod
import Theorems.Thm_Formalism_FG_InjVAux_hasOrd_one_of_cc
import Theorems.Thm_Formalism_FG_InjVAux_hasOrd_zero
import Theorems.Thm_Formalism_FG_InvIntVAux_eq_single_of_degree_eq_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_Formalism_LT_CoeffP_Bd_pow
import Theorems.Thm_Formalism_LT_LTL_Cong_pow
import Theorems.Thm_Formalism_LT_LTL_Near_pow


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries
open Pair TranslateJetMomentLawAnyIdempotentLevel
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution {R : Type} [CommRing R] {α τ : Type} [Fintype α] [DecidableEq α]
    {f : α → MvPowerSeries α R} (hf : Formalism.FG.IsIdMod2 f) {a : α → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (j : α) (x : τ) :
    coeff (Finsupp.single x 1) (subst a (f j)) = coeff (Finsupp.single x 1) (a j) := by
  have haS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst haS, finsum_eq_single _ (Finsupp.single j 1)]
  · rw [Finsupp.prod_single_index (by simp), hf.2 j j, if_pos rfl, one_smul, pow_one]
  · intro e he
    rcases Nat.lt_or_ge e.degree 2 with hlt | hge
    · rcases Nat.lt_or_ge e.degree 1 with h0 | h1
      · have : e = 0 := (Finsupp.degree_eq_zero_iff e).1 (by omega)
        subst this
        rw [coeff_zero_eq_constantCoeff_apply, hf.1 j, zero_smul]
      · obtain ⟨i, rfl⟩ := Formalism.FG.InjVAux.eq_single_of_degree_eq_one e (by omega)
        have hij : i ≠ j := fun hij => he (by rw [hij])
        rw [hf.2 j i, if_neg hij, zero_smul]
    · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      have hgood : ∀ i, Formalism.FG.InjVAux.Good 0 1 (a i) (a i) := fun i =>
        ⟨Formalism.FG.InjVAux.hasOrd_one_of_cc (ha i), Formalism.FG.InjVAux.hasOrd_one_of_cc (ha i), by
          rw [sub_self]; exact Formalism.FG.InjVAux.hasOrd_zero _⟩
      have hg := Formalism.FG.InjVAux.good_prod Finset.univ (fun i => 1 * e i) (fun i => a i ^ e i)
        (fun i => a i ^ e i) (fun i _ => (hgood i).pow (e i))
      have hsum : ∑ i ∈ Finset.univ, 1 * e i = e.degree := by
        rw [Finsupp.degree_eq_sum]; simp
      rw [hsum] at hg
      rw [hg.1 _ (by rw [Finsupp.degree_single]; omega), smul_zero]
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
