-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.depth_exists_last_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:37:54.198382+00:00
-- url     : https://prove2.me/submissions/5f7e09cb-fb59-407b-affc-7a06b3f40692

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depth_two_block_eq_sum_diff
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depthLastIff
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dominance_of_nabla_weight
import Theorems.Thm_Formalism_CohomologicalDescent_LD_block_weight_last_antitone
import Theorems.Thm_Formalism_CohomologicalDescent_LD_sum_lt_q_eq_sum_cast_add
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, w ≤ lam2 b)
    (μ : Fin (q + p) → ℕ) (x : MvPolynomial (Fin (q + p) × Fin (q + p)) ℤ)
    (hx : x ∈ nablaWt (q + p) (blockWtLast p q w lam2) μ) (hne : x ≠ 0) :
    ∃ i : ℕ, IsDepthLast p q w μ i ∧
      depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ = (i : ℤ) := by
  obtain ⟨hdom, htot⟩ := dominance_of_nabla_weight _ _ μ (block_weight_last_antitone p q w lam2 ha hb) x hx hne
  have h1 := hdom q
  rw [sum_lt_q_eq_sum_cast_add, sum_lt_q_eq_sum_cast_add] at h1
  have h2 : ∀ b : Fin q, blockWtLast p q w lam2 (Fin.castAdd p b) = lam2 b := fun b => Fin.append_left _ _ b
  simp only [h2] at h1
  refine ⟨∑ b, lam2 b - ∑ b : Fin q, μ (Fin.castAdd p b), ?_⟩
  have hiff := depthLastIff p q w (∑ b, lam2 b - ∑ b : Fin q, μ (Fin.castAdd p b)) lam2 μ htot
  have h3 : depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ =
      ((∑ b, lam2 b - ∑ b : Fin q, μ (Fin.castAdd p b) : ℕ) : ℤ) := by
    rw [depth_two_block_eq_sum_diff, Nat.cast_sub h1]
  exact ⟨hiff.mpr h3, h3⟩
end Formalism.CohomologicalDescent.LD
