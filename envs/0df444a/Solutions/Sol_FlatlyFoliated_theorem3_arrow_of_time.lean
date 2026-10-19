-- Prove2me | solution 1 for FlatlyFoliated.theorem3_arrow_of_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:26:02.333989+00:00
-- url     : https://prove2.me/submissions/9ac7c5ad-2262-4bd2-9735-10f1c4e72e74

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

theorem solution (Λ : ℝ) (hΛ : 0 < Λ) (μ : R3 → ℝ) (J : R3 → R3)
    (w : R3 → R3) (η : R3 → ℝ) (hμ : ContDiff ℝ ∞ μ) (hJ : ContDiff ℝ ∞ J)
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hμnn : ∀ x, 0 ≤ μ x)
    (hηpos : ∀ x, 0 < η x) (hsol : FFREquations Λ μ J w η) :
    (∀ x, 0 < divg w x / η x) ∨ (∀ x, divg w x / η x < 0) := by
  have hcomp : ∀ i, ContDiff ℝ ∞ (comp w i) := by
    intro i
    exact (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hw
  have hcont : Continuous (divg w) := by
    have : ContDiff ℝ ∞ (divg w) := by
      unfold divg; exact ContDiff.sum (fun i _ => pd_contDiff (hcomp i) i)
    exact this.continuous
  have hne : ∀ x, divg w x ≠ 0 := by
    intro x h0
    have h := (hsol x).1
    unfold Eq34 at h
    rw [h0] at h
    have hS : 0 ≤ ∑ i, ∑ j, (pd j (comp w i) x + pd i (comp w j) x) ^ 2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have hη2 : 0 < 1 / η x ^ 2 := by have := hηpos x; positivity
    have : (1 / η x ^ 2) * ((0:ℝ) ^ 2 - 1 / 4 * ∑ i, ∑ j,
        (pd j (comp w i) x + pd i (comp w j) x) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hη2.le (by nlinarith)
    have := hμnn x
    have := Real.pi_pos
    nlinarith
  by_contra hc
  push_neg at hc
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hc
  have hx' : divg w x < 0 := by
    rcases lt_or_gt_of_ne (hne x) with h | h
    · exact h
    · exact absurd hx (not_le.mpr (div_pos h (hηpos x)))
  have hy' : 0 < divg w y := by
    rcases lt_or_gt_of_ne (hne y) with h | h
    · exact absurd hy (not_le.mpr (div_neg_of_neg_of_pos h (hηpos y)))
    · exact h
  obtain ⟨z, hz⟩ := intermediate_value_univ x y hcont ⟨hx'.le, hy'.le⟩
  exact hne z hz
