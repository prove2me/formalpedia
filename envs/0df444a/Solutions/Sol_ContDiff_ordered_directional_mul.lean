-- Prove2me | solution 1 for ContDiff.ordered_directional_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:58:04.607274+00:00
-- url     : https://prove2.me/submissions/193eee99-94b1-438a-9484-7adceb6df595

import Theorems.Thm_ContDiff_iterate_directional_mul
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

open scoped ContDiff
set_option autoImplicit false

noncomputable def directional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (f : E → ℝ) : E → ℝ := fun x => fderiv ℝ f x a

theorem directional_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (directional a f) := by
  exact (hf.contDiff_fderiv_apply (m := ∞) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

theorem directional_iter_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (k : ℕ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ ((directional a)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => simpa only [Function.iterate_succ_apply'] using directional_smooth a ih

theorem directional_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (a : E) (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ j ∈ s, ContDiff ℝ ∞ (f j)) :
    directional a (fun x => ∑ j ∈ s, f j x) = fun x => ∑ j ∈ s, directional a (f j) x := by
  funext x
  simp only [directional, fderiv_fun_sum (fun j hj =>
    ((hf j hj).differentiable (by simp)).differentiableAt), ContinuousLinearMap.sum_apply]

theorem directional_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (c : ℝ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    directional a (fun x => c * f x) = fun x => c * directional a f x := by
  funext x
  simp only [directional, fderiv_const_mul ((hf.differentiable (by simp)).differentiableAt),
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem directional_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    directional a (fun x => f x * g x) =
      fun x => directional a f x * g x + f x * directional a g x := by
  funext x
  simp only [directional, fderiv_fun_mul ((hf.differentiable (by simp)).differentiableAt)
    ((hg.differentiable (by simp)).differentiableAt), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem directional_iter_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (a : E) (k : ℕ) (s : Finset ι) (c : ι → ℝ) (f : ι → E → ℝ)
    (hf : ∀ j ∈ s, ContDiff ℝ ∞ (f j)) :
    (directional a)^[k] (fun x => ∑ j ∈ s, c j * f j x) =
      fun x => ∑ j ∈ s, c j * ((directional a)^[k] (f j)) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, directional_sum]
    · funext x
      apply Finset.sum_congr rfl
      intro j hj
      rw [directional_const_mul a _ (directional_iter_smooth a _ (hf j hj))]
      simp only [Function.iterate_succ_apply']
    · intro j hj
      exact contDiff_const.mul (directional_iter_smooth a _ (hf j hj))

noncomputable def directionalFold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (a : Fin m → E) (β : Fin m → ℕ) (f : E → ℝ) : E → ℝ :=
  (List.finRange m).foldr (fun i g => (directional (a i))^[β i] g) f

theorem directionalFold_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (a : Fin (m+1) → E) (β : Fin (m+1) → ℕ) (f : E → ℝ) :
    directionalFold a β f = (directional (a 0))^[β 0]
      (directionalFold (Fin.tail a) (Fin.tail β) f) := by
  simp [directionalFold, List.finRange_succ, List.foldr_map, Fin.tail]

theorem directionalFold_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (a : Fin m → E) (β : Fin m → ℕ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (directionalFold a β f) := by
  induction m with
  | zero => simpa [directionalFold] using hf
  | succ m ih =>
    rw [directionalFold_succ]
    exact directional_iter_smooth _ _ (ih _ _)

theorem sum_Iic_cons {R : Type*} [AddCommMonoid R] {m : ℕ}
    (β : Fin (m+1) → ℕ) (F : (Fin (m+1) → ℕ) → R) :
    ∑ γ ∈ Finset.Iic β, F γ =
      ∑ j ∈ Finset.Iic (β 0), ∑ γ ∈ Finset.Iic (Fin.tail β), F (Fin.cons j γ) := by
  classical
  change (∑ γ ∈ Fintype.piFinset (fun i => Finset.Iic (β i)), F γ) = _
  have h := Finset.filter_piFinset_eq_map_consEquiv
    (fun i => Finset.Iic (β i)) (fun _ => True)
  simp only [Finset.filter_true] at h
  rw [h, Finset.sum_map, Finset.sum_product]
  rfl

theorem directionalFold_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (a : Fin m → E) (β : Fin m → ℕ) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    directionalFold a β (fun x => f x * g x) = fun x =>
      ∑ γ ∈ Finset.Iic β, (∏ i, (Nat.choose (β i) (γ i) : ℝ)) *
        (directionalFold a (fun i => β i - γ i) f x * directionalFold a γ g x) := by
  classical
  induction m with
  | zero =>
    have h : Finset.Iic β = {β} := by
      ext γ
      simp only [Finset.mem_Iic, Finset.mem_singleton]
      exact iff_of_true (fun i => Fin.elim0 i) (Subsingleton.elim _ _)
    simp [directionalFold, h]
  | succ m ih =>
    rw [directionalFold_succ, ih (Fin.tail a) (Fin.tail β), directional_iter_sum]
    · funext x
      have hm (γ : Fin m → ℕ) :
          (directional (a 0))^[β 0]
            (fun y => directionalFold (Fin.tail a) (fun i => Fin.tail β i - γ i) f y *
              directionalFold (Fin.tail a) γ g y) = fun y =>
          ∑ j ∈ Finset.range (β 0 + 1), ((β 0).choose j : ℝ) *
            (((directional (a 0))^[β 0-j]
                (directionalFold (Fin.tail a) (fun i => Fin.tail β i - γ i) f)) y *
             ((directional (a 0))^[j] (directionalFold (Fin.tail a) γ g)) y) :=
        ContDiff.iterate_directional_mul (a 0) (β 0) _ _
          (directionalFold_smooth _ _ hf) (directionalFold_smooth _ _ hg)
      simp_rw [hm]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm, sum_Iic_cons]
      change (∑ j ∈ Finset.range (β 0 + 1), _) = _
      rw [← Nat.range_succ_eq_Iic]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro γ hγ
      have ht : Fin.tail (fun i => β i - (Fin.cons j γ : Fin (m+1) → ℕ) i) =
          fun i => β i.succ - γ i := by funext i; simp [Fin.tail]
      simp [Fin.prod_univ_succ, directionalFold_succ, ht, Fin.tail_cons,
        Fin.tail, directional, mul_assoc, mul_left_comm]
    · intro γ hγ
      exact (directionalFold_smooth _ _ hf).mul (directionalFold_smooth _ _ hg)

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (a : Fin m → E) (β : Fin m → ℕ)
    (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    (List.finRange m).foldr
      (fun i h => (fun u y => fderiv ℝ u y (a i))^[β i] h) (fun y => f y * g y) x =
    ∑ γ ∈ Finset.Iic β, (∏ i, (Nat.choose (β i) (γ i) : ℝ)) *
      ((List.finRange m).foldr
        (fun i h => (fun u y => fderiv ℝ u y (a i))^[β i - γ i] h) f x *
       (List.finRange m).foldr
        (fun i h => (fun u y => fderiv ℝ u y (a i))^[γ i] h) g x) := by
  exact congrFun (directionalFold_mul a β hf hg) x
