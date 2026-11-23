-- Prove2me | solution 1 for Bl.b110.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:41.299141+00:00
-- url     : https://prove2.me/submissions/3d8c5ddc-6ffd-4c78-894d-e648c4da427e

import Mathlib
import Definitions.Def_Lemmata_B110_ExistsMoved
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.b110
private lemma exists_moved {n : Type} [DecidableEq n] (σ : Equiv.Perm n) (hσ : σ ≠ 1) (i : n) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_cases hi : σ i = i
  · obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra h
      exact hσ (Equiv.ext fun k => not_not.mp fun hk => h ⟨k, hk⟩)
    refine ⟨k, ?_, hk⟩
    rintro rfl
    exact hk hi
  · refine ⟨σ i, hi, ?_⟩
    intro h
    exact hi (σ.injective h)
end Bl.b110
end

set_option autoImplicit false
open Bl Bl.b110
namespace Bl.b110
theorem _root_.solution :
  ∀ {n : Type} [inst : Fintype.{0} n] [inst_1 : DecidableEq.{1} n] (A : Real → Matrix.{0, 0, 0} n n Complex)
  (A' : Matrix.{0, 0, 0} n n Complex),
  Eq.{1} (A 0) 1 →
    (∀ (i j : n), HasDerivAt.{0, 0} (fun (t : Real) ↦ A t i j) (A' i j) 0) →
      HasDerivAt.{0, 0} (fun (t : Real) ↦ Matrix.det.{0, 0} (A t)) (Matrix.trace.{0, 0} A') 0 := by
  intro n _ _ A A' h0 hd
  have hfun : (fun t : ℝ => Matrix.det (A t)) =
      fun t => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i := by
    funext t
    exact Matrix.det_apply' _
  rw [hfun]
  have hprod : ∀ σ : Equiv.Perm n, HasDerivAt (fun t : ℝ => ∏ i, A t (σ i) i)
      (∑ i, (∏ j ∈ Finset.univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 := by
    intro σ
    exact HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i t => A t (σ i) i)
      (fun i _ => hd (σ i) i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun σ _ => (hprod σ).const_mul (((Equiv.Perm.sign σ : ℤ) : ℂ)))
  refine hsum.congr_deriv ?_
  rw [Finset.sum_eq_single (1 : Equiv.Perm n)]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply,
      h0, smul_eq_mul, Matrix.trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.prod_eq_one, one_mul]
    · rfl
    intro j _
    simp
  · intro σ _ hσ
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    obtain ⟨j, hji, hj⟩ := exists_moved σ hσ i
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩), zero_smul]
    rw [h0]
    exact Matrix.one_apply_ne hj
  · intro h
    exact absurd (Finset.mem_univ _) h
end Bl.b110
