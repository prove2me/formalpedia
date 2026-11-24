-- Prove2me | solution 1 for Formalism.L2.Th1.H.expFPS_radius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:29:14.323742+00:00
-- url     : https://prove2.me/submissions/d9e5179c-8ea8-42da-a7f5-4903748d23e2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
import Theorems.Thm_Formalism_L2_Th1_H_norm_expTerm_mul_le
import Theorems.Thm_Formalism_L2_Th1_H_summable_norm_expTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ)
    (h : ∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖l x‖)) : (expFPS c l).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hb : ∀ n, ‖expFPS c l n‖ * (r : ℝ) ^ n ≤
      (∑' x, ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖)) * (1 / 2 : ℝ) ^ n := by
    intro n
    have hs := summable_norm_expTerm c l h n
    have h1 : ‖expFPS c l n‖ ≤ ∑' x, ‖expTerm c l n x‖ := norm_tsum_le_tsum_norm hs
    have h2 : ∀ x, ‖expTerm c l n x‖ * (r : ℝ) ^ n ≤
        ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖) * (1 / 2 : ℝ) ^ n := by
      intro x
      have h3 := norm_expTerm_mul_le c l n x (2 * (r : ℝ)) (by positivity)
      have e : ‖expTerm c l n x‖ * (r : ℝ) ^ n =
          ‖expTerm c l n x‖ * (2 * (r : ℝ)) ^ n * (1 / 2 : ℝ) ^ n := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    calc ‖expFPS c l n‖ * (r : ℝ) ^ n ≤ (∑' x, ‖expTerm c l n x‖) * (r : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ∑' x, ‖expTerm c l n x‖ * (r : ℝ) ^ n := tsum_mul_right.symm
      _ ≤ ∑' x, ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖) * (1 / 2 : ℝ) ^ n :=
          Summable.tsum_le_tsum h2 (hs.mul_right _) ((h (2 * (r : ℝ))).mul_right _)
      _ = (∑' x, ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖)) * (1 / 2 : ℝ) ^ n := tsum_mul_right
  exact Summable.of_nonneg_of_le (fun n => by positivity) hb (summable_geometric_two.mul_left _)
end Formalism.L2.Th1.H
