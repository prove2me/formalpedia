-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.excessGainBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:24.545188+00:00
-- url     : https://prove2.me/submissions/857d6f54-95d2-49b9-8709-0adf11064210

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_QuadraticExponentIdentity
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ABArith
import Theorems.Thm_Formalism_GrowthSums_oddPowerInvSumIdentity


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
theorem _root_.solution : ExcessGainBound := by
  intro n p TT D al cap de v i ch E hp hal hcap hi0 hch0 hE hchD hv hD hnD
  have hp0 : 0 < p := by linarith
  obtain ⟨hgs, -⟩ := Formalism.GrowthSums.oddPowerInvSumIdentity p hp
  have key : ∀ s ∈ TT, (∑' e : ℕ, (if 2 * e + 1 ∈ D s then 0 else
      max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0)) ≤
      gamP p * al s - ∑ e ∈ E, ch s e - ∑ e ∈ E, i s e := by
    intro s hs
    have hA : HasSum (fun e : ℕ => al s / p ^ (2 * e + 1)) (gamP p * al s) := by
      have h := hgs.mul_right (al s)
      have hf : (fun e : ℕ => al s / p ^ (2 * e + 1)) =
          fun e : ℕ => (p ^ (2 * e + 1))⁻¹ * al s := by
        funext e
        rw [div_eq_mul_inv, mul_comm]
      rw [hf]
      exact h
    have hC : HasSum (fun e : ℕ => ch s e) (∑ e ∈ E, ch s e) :=
      hasSum_sum_of_ne_finset_zero (fun e he => (hE s e he).2)
    have hI : HasSum (fun e : ℕ => i s e) (∑ e ∈ E, i s e) :=
      hasSum_sum_of_ne_finset_zero (fun e he => (hE s e he).1)
    have hR := (hA.sub hC).sub hI
    have hpos : ∀ e : ℕ, 0 ≤ al s / p ^ (2 * e + 1) :=
      fun e => div_nonneg (hal s) (pow_nonneg hp0.le _)
    have hsum : Summable (fun e : ℕ => (if 2 * e + 1 ∈ D s then (0 : ℝ) else
        max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0)) := by
      refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hA.summable
      · split_ifs
        · exact le_rfl
        · exact le_max_right _ _
      · split_ifs
        · exact hpos e
        · exact max_le (by linarith [hcap (s + ((2 * e + 1 : ℕ) : ZMod n))]) (hpos e)
    refine hasSum_le (fun e => ?_) hsum.hasSum hR
    split_ifs with h
    · have := hD s hs e h
      linarith
    · have h1 := hnD s hs e h
      have h2 := hchD s e h
      have h3 := le_trans h1 (min_le_left _ _)
      have h4 := le_trans h1 (min_le_right _ _)
      rw [h2]
      exact max_le (by linarith) (by linarith)
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  unfold excessGain
  linarith
end Formalism.InvariantFactorPaths.G7
