-- Prove2me | solution 1 for FirstOrderOpt.FiniteSum.gradient_variation_bound
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T17:27:38.354647+00:00
-- url     : https://prove2.me/submissions/dcf667ce-e38b-4398-813b-b8045e02138b

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic
open scoped BigOperators

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (X : Set E) (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x)
    (fi : Fin m → E → ℝ) (hf : ∀ x, f x = (1 / (m : ℝ)) * ∑ i, fi i x)
    (gradf : Fin m → E → E →L[ℝ] ℝ)
    (L : Fin m → ℝ) (hL : ∀ i, 0 < L i)
    (hsmooth : ∀ i x y, ‖gradf i x - gradf i y‖ ≤ L i * ‖x - y‖)
    (q : Fin m → ℝ) (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1)
    (LQ : ℝ) (hLQ : LQ = (1 / (m : ℝ)) * Finset.univ.sup' hne (fun i => L i / q i))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y),
    ∀ x ∈ X, (1 / (m : ℝ)) * ∑ i, (1 / ((m : ℝ) * q i)) * ‖gradf i x - gradf i xstar‖ ^ 2 ≤
      2 * LQ * (Ψ x - Ψ xstar)) := by
  intro H
  let I : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
  have hI : ‖I‖ = 1 := by simp [I]
  have hs : ∀ (i : Fin 1) (x y : ℝ), ‖x • I - y • I‖ ≤ 1 * ‖x - y‖ := by
    intro i x y
    erw [← sub_smul, norm_smul, hI]
    simp
  have h := @H ℝ _ _ 1 (by simp) Set.univ (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (by simp) (fun _ _ => 0) (by simp) (fun _ x => x • I)
    (fun _ => 1) (by norm_num) hs (fun _ => 1) (by norm_num) (by simp)
    1 (by simp) 0 (by simp) (by simp) 1 (by simp)
  norm_num [hI] at h
