-- Prove2me | solution 1 for FlatlyFoliated.identity_82_83
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:24:25.556157+00:00
-- url     : https://prove2.me/submissions/e1bd86db-1132-4fe7-9a08-f816a3182fd3

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic


open scoped ContDiff
open FlatlyFoliated

namespace FFAux

lemma pd_contDiff {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) : ContDiff ℝ ∞ (pd i u) := by
  unfold pd
  exact (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma pd_diff {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) : Differentiable ℝ (pd i u) :=
  (pd_contDiff hu i).differentiable (by simp)

lemma pd_comm {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i j : Fin 3) (x : R3) :
    pd i (pd j u) x = pd j (pd i u) x := by
  have key : ∀ a b : Fin 3, pd a (pd b u) x =
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro a b
    unfold pd
    have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
      ((hu.fderiv_right (m := 1) (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num | decide)).differentiable (by simp)) x
    have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single b (1:ℝ)) x)
    rw [h.fderiv]
    first | rfl | simp
  rw [key, key]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) _ _

lemma pd_mul {f g : R3 → ℝ} (i : Fin 3) (x : R3)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x := by
  unfold pd
  rw [(hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv]
  simp; ring

lemma pd_sub {f g : R3 → ℝ} (i : Fin 3) (x : R3)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  unfold pd
  rw [(hf.hasFDerivAt.fun_sub hg.hasFDerivAt).fderiv]
  simp

lemma pd_sum {f : Fin 3 → R3 → ℝ} (i : Fin 3) (x : R3)
    (hf : ∀ k, DifferentiableAt ℝ (f k) x) :
    pd i (fun y => ∑ k, f k y) x = ∑ k, pd i (f k) x := by
  unfold pd
  rw [(HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hf k).hasFDerivAt)).fderiv]
  simp

lemma pd_coord (i j : Fin 3) (c : ℝ) (x : R3) :
    pd i (fun y : R3 => c * y j) x = if i = j then c else 0 := by
  unfold pd
  have : (fun y : R3 => c * y j) = fun y => c * (EuclideanSpace.proj j : R3 →L[ℝ] ℝ) y := rfl
  rw [this, (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt (x := x)).const_mul c).fderiv]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

end FFAux


open FlatlyFoliated FFAux

theorem solution (Λ : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    ∑ j, pd j (fun y => lap f y * pd j f y - ∑ i, pd j (pd i f) y * pd i f y
        - (2 * Λ / 3) * y j) x =
      lap f x ^ 2 - hessNormSq f x - 2 * Λ := by
  have c1 : ∀ i, ContDiff ℝ ∞ (pd i f) := fun i => pd_contDiff hf i
  have c2 : ∀ i j, ContDiff ℝ ∞ (pd j (pd i f)) := fun i j => pd_contDiff (c1 i) j
  have hlap : ContDiff ℝ ∞ (lap f) := by
    unfold lap; exact ContDiff.sum (fun i _ => c2 i i)
  have dlap : Differentiable ℝ (lap f) := hlap.differentiable (by
    first | exact WithTop.coe_le_coe.mpr le_top | norm_num)
  have d1 : ∀ i, Differentiable ℝ (pd i f) := fun i => pd_diff hf i
  have d2 : ∀ i j, Differentiable ℝ (pd j (pd i f)) := fun i j => pd_diff (c1 i) j
  have hcoord : ∀ j, DifferentiableAt ℝ (fun y : R3 => (2 * Λ / 3) * y j) x := by
    intro j
    exact (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).differentiableAt).const_mul _)
  have step : ∀ j, pd j (fun y => lap f y * pd j f y - ∑ i, pd j (pd i f) y * pd i f y
        - (2 * Λ / 3) * y j) x =
      (pd j (lap f) x * pd j f x + lap f x * pd j (pd j f) x) -
        ∑ i, (pd j (pd j (pd i f)) x * pd i f x + pd j (pd i f) x * pd j (pd i f) x)
        - 2 * Λ / 3 := by
    intro j
    have dA : DifferentiableAt ℝ (fun y => lap f y * pd j f y) x := (dlap x).mul (d1 j x)
    have dB : DifferentiableAt ℝ (fun y => ∑ i, pd j (pd i f) y * pd i f y) x :=
      DifferentiableAt.fun_sum (fun i _ => (d2 i j x).mul (d1 i x))
    rw [pd_sub (f := fun y => lap f y * pd j f y - ∑ i, pd j (pd i f) y * pd i f y)
      (g := fun y => (2 * Λ / 3) * y j) j x (dA.sub dB) (hcoord j)]
    rw [pd_sub (f := fun y => lap f y * pd j f y)
      (g := fun y => ∑ i, pd j (pd i f) y * pd i f y) j x dA dB]
    rw [pd_mul j x (dlap x) (d1 j x), pd_coord, if_pos rfl]
    congr 2
    rw [pd_sum (f := fun i y => pd j (pd i f) y * pd i f y) j x (fun i => (d2 i j x).mul (d1 i x))]
    exact Finset.sum_congr rfl (fun i _ => pd_mul j x (d2 i j x) (d1 i x))
  rw [Finset.sum_congr rfl (fun j _ => step j)]
  -- third derivatives commute
  have h3 : ∀ j : Fin 3, pd j (lap f) x * pd j f x = ∑ i, pd i (pd i (pd j f)) x * pd j f x := by
    intro j
    have : pd j (lap f) x = ∑ i, pd j (pd i (pd i f)) x := by
      unfold lap; exact pd_sum (f := fun i => pd i (pd i f)) j x (fun i => d2 i i x)
    rw [this, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pd_comm (c1 i) j i x]
    have : pd j (pd i f) = pd i (pd j f) := funext (pd_comm hf j i)
    rw [this]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun j _ => h3 j)]
  rw [Finset.sum_comm (f := fun j i => pd j (pd j (pd i f)) x * pd i f x)]
  have hl : ∑ j, lap f x * pd j (pd j f) x = lap f x ^ 2 := by
    rw [← Finset.mul_sum, sq]; rfl
  have hh : ∑ j, ∑ i, pd j (pd i f) x * pd j (pd i f) x = hessNormSq f x := by
    unfold hessNormSq
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => (sq _).symm))
  rw [hl, hh]
  ring
