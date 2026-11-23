-- Prove2me | solution 1 for Formalism.REAL.prod_factorial_support_sub_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:13.363072+00:00
-- url     : https://prove2.me/submissions/1d011454-cf28-468c-8b75-f71615139a74

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {σ : Type*}
namespace Formalism.REAL
theorem _root_.solution [DecidableEq σ] (u : σ →₀ ℕ) (v : σ) (hv : u v ≠ 0) :
    (∏ k ∈ u.support, (u k).factorial) =
      u v * ∏ k ∈ (u - Finsupp.single v 1 : σ →₀ ℕ).support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial := by
  have hsub : (u - Finsupp.single v 1 : σ →₀ ℕ).support ⊆ u.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro h0; apply hk; simp [Finsupp.tsub_apply, h0]
  have e : ∏ k ∈ (u - Finsupp.single v 1 : σ →₀ ℕ).support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ u.support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial :=
    Finset.prod_subset hsub (fun k _ hk => by rw [Finsupp.notMem_support_iff.mp hk]; rfl)
  rw [e]
  have hmem : v ∈ u.support := Finsupp.mem_support_iff.mpr hv
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem]
  have h2 : ∏ k ∈ u.support.erase v, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ u.support.erase v, (u k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k ≠ v := Finset.ne_of_mem_erase hk
    simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm hk']
  rw [h2, ← mul_assoc]
  congr 1
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
  exact (Nat.mul_factorial_pred hv).symm
end Formalism.REAL
