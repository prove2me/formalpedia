-- Prove2me | solution 1 for Bl.ProductIdentities.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:37.269799+00:00
-- url     : https://prove2.me/submissions/2bdc9b80-8c70-478d-b838-8e1c5b608da8

import Mathlib
import Definitions.Def_Lemmata_ProductIdentities_ProdInvZpowMulOfProdZpowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.ProductIdentities
private lemma prod_erase_one_perm_apply_eq_zero {n : Type} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) (hσ : σ ≠ 1)
    (k : n) : ∏ j ∈ Finset.univ.erase k, (1 : Matrix n n ℂ) (σ j) j = 0 := by
  have hex : ∃ j, j ≠ k ∧ σ j ≠ j := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    apply hσ
    ext x
    simp only [Equiv.Perm.coe_one, id_eq]
    by_cases hx : x = k
    · subst hx
      by_contra hk
      exact hk (σ.injective (h (σ x) hk))
    · exact h x hx
  obtain ⟨j, hjk, hj⟩ := hex
  apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩)
  simp [hj]
end Bl.ProductIdentities
end

set_option autoImplicit false
open Bl Bl.ProductIdentities
namespace Bl.ProductIdentities
theorem _root_.solution :
  ∀ {n : Type} [inst : Fintype.{0} n] [inst_1 : DecidableEq.{1} n] (A : Real → Matrix.{0, 0, 0} n n Complex)
  (A' : Matrix.{0, 0, 0} n n Complex),
  Eq.{1} (A 0) 1 →
    (∀ (i j : n), HasDerivAt.{0, 0} (fun (t : Real) ↦ A t i j) (A' i j) 0) →
      HasDerivAt.{0, 0} (fun (t : Real) ↦ Matrix.det.{0, 0} (A t)) (Matrix.trace.{0, 0} A') 0 := by
  intro n _ _ A A' h0 hd
  have key : ∀ σ : Equiv.Perm n, HasDerivAt
      (fun t : ℝ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ k, (∏ j ∈ Finset.univ.erase k, A 0 (σ j) j) • A' (σ k) k) 0 := by
    intro σ
    apply HasDerivAt.const_mul
    exact HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i t => A t (σ i) i)
      (f' := fun i => A' (σ i) i) (fun k _ => hd (σ k) k)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => key σ)
  have hfun : (fun t : ℝ => Matrix.det (A t)) =
      fun t => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i := by
    funext t
    exact Matrix.det_apply' _
  rw [hfun]
  refine hsum.congr_deriv ?_
  rw [Finset.sum_eq_single (1 : Equiv.Perm n)]
  · rw [h0]
    simp [Matrix.trace, Matrix.one_apply]
  · intro σ _ hσ
    rw [h0, Finset.sum_eq_zero (fun k _ => by rw [prod_erase_one_perm_apply_eq_zero σ hσ k, zero_smul]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Bl.ProductIdentities
