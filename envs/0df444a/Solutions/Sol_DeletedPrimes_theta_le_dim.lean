-- Prove2me | solution 1 for DeletedPrimes.theta_le_dim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:14:50.299961+00:00
-- url     : https://prove2.me/submissions/16316c5b-a8da-4cb8-bc9d-8b255949022a

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_dim_nonneg
import Theorems.Thm_DeletedPrimes_summable_units
import Theorems.Thm_DeletedPrimes_abs_err_le_rankin
import Theorems.Thm_DeletedPrimes_theta_le_of_isRegular
import Theorems.Thm_DeletedPrimes_theta_le_one


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (hS : ∀ p ∈ S, p.Prime)
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    theta S ≤ dim S := by
  refine le_of_forall_gt_imp_ge_of_dense fun σ hσ => ?_
  by_cases hσ1 : 1 ≤ σ
  · exact le_trans (theta_le_one S) hσ1
  · push Not at hσ1
    have hσ0 : 0 ≤ σ := le_trans (dim_nonneg S) hσ.le
    have hsum := summable_units hσ
    exact theta_le_of_isRegular hσ0
      ⟨2 * unitSum S σ, fun x hx => abs_err_le_rankin hS hsum hσ0 hσ1.le h1 hx⟩
end DeletedPrimes
