-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.norm_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:52.905685+00:00
-- url     : https://prove2.me/submissions/cfefa8c1-962d-4549-9381-eff3c4f70c9e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
namespace TraceNormBounds
section Normed
variable {K : Type} [NormedField K] [IsUltrametricDist K]
private lemma norm_finset_sum_le_one_of_norm_le_one {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))
private lemma norm_natCast_le_one_kummer_theta_logarithms (n : ℕ) : ‖(n : K)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))
private lemma int_lemma_3 (z : ℤ) : ‖(z : K)‖ ≤ 1 := by
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · exact_mod_cast norm_natCast_le_one_kummer_theta_logarithms n
  · rw [Int.cast_neg, norm_neg]
    exact_mod_cast norm_natCast_le_one_kummer_theta_logarithms n
end Normed
end TraceNormBounds
open TraceNormBounds
end Formalism.L2.Th1.D
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution (Q : Polynomial ℤ) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖Polynomial.eval₂ (Int.castRingHom K) x Q‖ ≤ 1 := by
  rw [Polynomial.eval₂_eq_sum_range]
  apply norm_finset_sum_le_one_of_norm_le_one
  intro i _
  have hc : ‖(Int.castRingHom K) (Q.coeff i)‖ ≤ 1 := by
    rw [eq_intCast]
    exact int_lemma_3 _
  have hp : ‖x ^ i‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | exact pow_le_one _ (norm_nonneg _) hx
  rw [norm_mul]
  first
  | exact mul_le_one₀ hc (norm_nonneg _) hp
  | exact mul_le_one' hc hp
  | nlinarith [norm_nonneg ((Int.castRingHom K) (Q.coeff i)), norm_nonneg (x ^ i)]
end Formalism.L2.Th1.D.TraceNormBounds
