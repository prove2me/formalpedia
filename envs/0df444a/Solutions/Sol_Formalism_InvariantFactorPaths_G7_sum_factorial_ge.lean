-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.sum_factorial_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:05.64999+00:00
-- url     : https://prove2.me/submissions/66e9cf09-8c4a-4919-8219-32013a0cea81

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_QuadraticExponentIdentity
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ABArith
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lgN_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_factorialValuationLowerBound

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {ι : Type} (p : ℕ) (hp : p.Prime) (T : Finset ι) (f : ι → ℕ) (B : ℕ)
    (hB : ∀ x ∈ T, f x ≤ B) :
    ((∑ x ∈ T, f x : ℕ) : ℝ) / ((p : ℝ) - 1) - (T.card : ℝ) * lgN p B ≤
      ∑ x ∈ T, (padicValNat p (f x).factorial : ℝ) := by
  have h1 : ∑ x ∈ T, ((f x : ℝ) / ((p : ℝ) - 1) - lgN p B) ≤
      ∑ x ∈ T, (padicValNat p (f x).factorial : ℝ) := by
    apply Finset.sum_le_sum
    intro x hx
    have h := factorialValuationLowerBound p (f x) hp
    have h' : (lgN p (f x) : ℝ) ≤ lgN p B := by exact_mod_cast lgN_mono p (hB x hx)
    linarith
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_const, nsmul_eq_mul] at h1
  rw [Nat.cast_sum]
  exact h1
end Formalism.InvariantFactorPaths.G7
