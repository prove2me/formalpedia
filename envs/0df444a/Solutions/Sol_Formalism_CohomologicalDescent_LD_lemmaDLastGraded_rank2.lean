-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.lemmaDLastGraded_rank2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:12.129841+00:00
-- url     : https://prove2.me/submissions/eaec39c3-1231-4d6b-9c18-b15ef2424853

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_block_weight_last_one_one
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dn2
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dnNeZero
import Theorems.Thm_Formalism_CohomologicalDescent_LD_expLeIffKilled
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_gen_mem_weyl
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank2Exact
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank2Other
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
theorem _root_.solution : LemmaDLastGraded_rank2 := by
  intro l w y M ξ hl hwy hyM _ i' e _ i μ hd _
  have hd' : μ 1 = w + i := by simpa [IsDepthLast] using hd
  rw [block_weight_last_one_one]
  show ExpLe l 2 (wt2 y w) μ (e + padicValInt l (Dn 1 (M - w) i fun _ : Fin 1 => M - y))
  rw [expLeIffKilled l 2 _ μ e _ hl (dnNeZero 1 (M - w) i 1 _)]
  intro x hx
  refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
  by_cases hex : ∃ j, w + j ≤ y ∧ μ = wt2 (y - j) (w + j)
  · obtain ⟨j, hj, rfl⟩ := hex
    have hd'' : w + j = w + i := hd'
    have hij : j = i := by omega
    subst hij
    rw [(rank2Exact y w j hj).1] at hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [dn2 1 (M - w) (M - y) j le_rfl (by omega), smul_smul]
    have hyw : M - w - (M - y) = y - w := by omega
    rw [hyw]
    have : (1 * ((l : ℤ) ^ e * ((j.factorial * (y - w).choose j : ℕ) : ℤ)) * c) =
        ((l : ℤ) ^ e * (j.factorial : ℤ) * c) * ((y - w).choose j : ℤ) := by
      push_cast
      ring
    rw [this, mul_smul]
    exact Submodule.smul_mem _ _ (ld_gen_mem_weyl y w j)
  · have hbot := rank2Other y w μ hwy (fun j hj hμ => hex ⟨j, hj, hμ⟩)
    rw [hbot] at hx
    rw [(Submodule.mem_bot ℤ).mp hx, smul_zero]
    exact Submodule.zero_mem _
end Formalism.CohomologicalDescent.LD
