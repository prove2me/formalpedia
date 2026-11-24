-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.phE_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:07:48.68653+00:00
-- url     : https://prove2.me/submissions/e45d7c17-db62-43e4-a4db-c4fda3a948c9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_phE_apply_inl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_phE_apply_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) (ζ : D.EM) : D.phE p ζ = ζ.sum fun x k => k • D.varE p x := by
  classical
  ext ⟨i, a⟩
  rw [Finsupp.sum_fintype _ _ (by intro x; simp), Finsupp.finsetSum_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rcases i with b | t
  · rw [phE_apply_inl]
    simp [varE, Finsupp.single_apply, mb, ite_and]
  · rw [phE_apply_inr]
    simp only [varE, Sum.elim_inl, Sum.elim_inr, Finsupp.smul_apply, Finsupp.single_apply, Prod.mk.injEq,
      Sum.inr.injEq, reduceCtorEq, false_and, if_false, Finset.sum_const_zero, zero_add,
      ite_and, smul_eq_mul, mul_ite, mul_one, mul_zero, mlab, mw, mtp]
    have key : ∀ f : D.Tau → Fin D.r → ℕ,
        (∑ x, ∑ y, if x = t then (if y = a then f x y else 0) else 0) = f t a := by
      intro f
      rw [Finset.sum_eq_single t (by intro x _ hx; simp [hx]) (by simp)]
      simp
    rw [key, key, key]
    ring
end Formalism.MainNotions.PlaneGram.TwistData
