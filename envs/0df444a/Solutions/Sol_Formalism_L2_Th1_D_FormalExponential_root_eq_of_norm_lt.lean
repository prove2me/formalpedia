-- Prove2me | solution 1 for Formalism.L2.Th1.D.FormalExponential.root_eq_of_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:42.522882+00:00
-- url     : https://prove2.me/submissions/ab2eb1b4-32de-4a23-b80e-056cc6aa985e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_norm_eq_one_of_pow
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_norm_pow_sub_pow_le
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_one_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_funEq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_subst_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_rescale_lgF


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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws (constantCoeff_lgF coeff_one_lgF lgF_subst_inj lgF_funEq map_lgF
  rescale_lgF)
open Formalism.L2.Th1.D.FormalExponential
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.D.FormalExponential
theorem _root_.solution {a b : K} {N : ℕ} (hN : ‖(N : K)‖ = 1) (ha : a ^ N = 1)
    (hb : b ^ N = 1) (hab : ‖a - b‖ < 1) : a = b := by
  by_contra hne
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have na : ‖a‖ = 1 := norm_eq_one_of_pow hN0 ha
  have nb : ‖b‖ = 1 := norm_eq_one_of_pow hN0 hb
  have hS : (∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) = 0 := by
    have h := geom_sum₂_mul a b N
    rw [ha, hb, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have hT : (∑ i ∈ Finset.range N, b ^ i * b ^ (N - 1 - i)) = (N : K) * b ^ (N - 1) := by
    rw [Finset.sum_congr rfl (g := fun _ => b ^ (N - 1))]
    · simp
    · intro i hi
      have : i < N := Finset.mem_range.1 hi
      rw [← pow_add]
      congr 1
      omega
  have hD : (N : K) * b ^ (N - 1) =
      - ∑ i ∈ Finset.range N, (a ^ i - b ^ i) * b ^ (N - 1 - i) := by
    simp only [sub_mul, Finset.sum_sub_distrib, hS, hT]
    ring
  have h1 : ‖(N : K) * b ^ (N - 1)‖ = 1 := by
    rw [norm_mul, norm_pow, hN, nb, one_pow, one_mul]
  have h2 : ‖(N : K) * b ^ (N - 1)‖ ≤ ‖a - b‖ := by
    rw [hD, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul, norm_pow, nb, one_pow, mul_one]
    exact norm_pow_sub_pow_le na.le nb.le i
  rw [h1] at h2
  exact absurd hab (not_lt.2 h2)
end Formalism.L2.Th1.D.FormalExponential
