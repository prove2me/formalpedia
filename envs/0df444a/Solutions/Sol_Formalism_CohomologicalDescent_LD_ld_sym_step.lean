-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_sym_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:06:15.04148+00:00
-- url     : https://prove2.me/submissions/6c837d91-6203-4e8f-b2c1-112b720a524d

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_coeff_lin
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_rowGen

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
theorem _root_.solution (q w : ℕ) (μ : Fin (1 + q) → ℕ) (S : Finset (Fin (1 + q))) (a : Fin (1 + q))
    (ha : a ∉ S) (hz : ldZ q ∉ S) :
    rowDiv ℤ a (ldZ q) (μ a) (ldSv q w μ S) =
      ((w - ∑ b ∈ S, μ b).choose (μ a) : ℤ) • ldSv q w μ (insert a S) := by
  have hg : rowGen ℤ a (ldZ q) (ldSv q w μ S) =
      (Polynomial.C (X (ldZ q, ldZ q)) + Polynomial.X * Polynomial.C (X (a, ldZ q))) ^ (w - ∑ b ∈ S, μ b) *
        Polynomial.C (∏ b ∈ S, X (b, ldZ q) ^ μ b) := by
    unfold ldSv
    rw [map_mul, map_pow, ld_sym_rowGen, if_pos rfl, map_prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    have hbz : ¬ (b, ldZ q).1 = ldZ q := fun h => hz (h ▸ hb)
    rw [map_pow, ld_sym_rowGen, if_neg hbz, add_zero, map_pow]
  unfold rowDiv
  rw [hg, ld_coeff_lin]
  unfold ldSv
  rw [Finset.sum_insert ha, Finset.prod_insert ha, zsmul_eq_mul, add_comm (μ a), Nat.sub_add_eq]
  push_cast
  ring
end Formalism.CohomologicalDescent.LD
