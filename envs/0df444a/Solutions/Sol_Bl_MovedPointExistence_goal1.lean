-- Prove2me | solution 1 for Bl.MovedPointExistence.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:34.883802+00:00
-- url     : https://prove2.me/submissions/b30f306b-afb5-4f6e-853b-f824df35b7a4

import Mathlib
import Definitions.Def_Lemmata_MovedPointExistence_ExistsMoved
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Matrix
open NormedSpace
namespace Bl.MovedPointExistence
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private lemma exists_moved (σ : Equiv.Perm ι) (hσ : σ ≠ 1) (i : ι) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
    by_contra hc
    push Not at hc
    exact hσ (Equiv.ext fun x => by simpa using hc x)
  by_cases hi : σ i = i
  · refine ⟨k, ?_, hk⟩
    rintro rfl
    exact hk hi
  · refine ⟨σ i, hi, ?_⟩
    intro h2
    exact hi (σ.injective h2)
end Bl.MovedPointExistence
end

set_option autoImplicit false
open Finset Matrix
open NormedSpace
open Bl Bl.MovedPointExistence
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Bl.MovedPointExistence
theorem _root_.solution (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  have hfun : (fun t => (A t).det) =
      fun t => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i := by
    funext t
    exact Matrix.det_apply' (A t)
  rw [hfun]
  have key : ∀ σ : Equiv.Perm ι,
      HasDerivAt (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
        (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∑ i, (∏ j ∈ univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 := by
    intro σ
    exact (HasDerivAt.fun_finsetProd (u := univ) (fun i _ => h (σ i) i)).const_mul _
  have hs := HasDerivAt.fun_sum (u := univ) (fun σ _ => key σ)
  refine hs.congr_deriv ?_
  rw [h0, Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp only [Matrix.trace, Matrix.diag_apply, Equiv.Perm.sign_one, Units.val_one, Int.cast_one,
      one_mul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_eq_one (fun j _ => ?_), one_mul]
    · rfl
    · rw [Equiv.Perm.one_apply, Matrix.one_apply_eq]
  · intro σ _ hσ
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    obtain ⟨j, hji, hj⟩ := exists_moved σ hσ i
    have hz : ∏ l ∈ univ.erase i, (1 : Matrix ι ι ℂ) (σ l) l = 0 :=
      Finset.prod_eq_zero (i := j) (by simp [hji]) (Matrix.one_apply_ne hj)
    rw [hz, zero_smul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn
end Bl.MovedPointExistence
