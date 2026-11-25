-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_rank2_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:32.046558+00:00
-- url     : https://prove2.me/submissions/03714383-f723-4f5d-832c-2bd0d1d5fdb9

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dnNeZero
import Theorems.Thm_Formalism_CohomologicalDescent_LD_expLeIffKilled
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dn2
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank2Other
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_gen_mem_weyl
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank2Exact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (l w y : ℕ) (hl : l.Prime) (hy : y ≤ w) (e i : ℕ) (μ : Fin 2 → ℕ)
    (hd : μ 0 + i = w) :
    ExpLe l 2 (wt2 w y) μ (e + padicValInt l (Dn 1 w i (fun _ : Fin 1 => y))) := by
  rw [expLeIffKilled l 2 _ μ e _ hl (dnNeZero 1 w i 1 _)]
  intro x hx
  refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
  by_cases hex : ∃ j, y + j ≤ w ∧ μ = wt2 (w - j) (y + j)
  · obtain ⟨j, hj, rfl⟩ := hex
    have hd' : w - j + i = w := hd
    have hij : j = i := by omega
    subst hij
    rw [(rank2Exact w y j hj).1] at hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [dn2 1 w y j le_rfl hj, smul_smul]
    have : (1 * ((l : ℤ) ^ e * ((j.factorial * (w - y).choose j : ℕ) : ℤ)) * c) =
        ((l : ℤ) ^ e * (j.factorial : ℤ) * c) * ((w - y).choose j : ℤ) := by
      push_cast
      ring
    rw [this, mul_smul]
    exact Submodule.smul_mem _ _ (ld_gen_mem_weyl w y j)
  · have hbot := rank2Other w y μ hy (fun j hj hμ => hex ⟨j, hj, hμ⟩)
    rw [hbot] at hx
    rw [(Submodule.mem_bot ℤ).mp hx, smul_zero]
    exact Submodule.zero_mem _
end Formalism.CohomologicalDescent.LD
