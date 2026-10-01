-- Prove2me | solution 1 for FirstOrderOpt.FiniteSum.variance_reduced_estimator_bound
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T17:27:57.380983+00:00
-- url     : https://prove2.me/submissions/713c429a-b3b2-4136-bd8d-6b30b2bdb3d2

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic
open scoped BigOperators

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (X : Set E) (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x)
    (fi : Fin m → E → ℝ) (hf : ∀ x, f x = (1 / (m : ℝ)) * ∑ i, fi i x)
    (gradf : Fin m → E → E →L[ℝ] ℝ)
    (gradf_full : E → E →L[ℝ] ℝ)
    (hgradf_avg : ∀ x, gradf_full x = (1 / (m : ℝ)) • ∑ i, gradf i x)
    (L : Fin m → ℝ) (hL : ∀ i, 0 < L i)
    (hsmooth : ∀ i x y, ‖gradf i x - gradf i y‖ ≤ L i * ‖x - y‖)
    (q : Fin m → ℝ) (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1)
    (LQ : ℝ) (hLQ : LQ = (1 / (m : ℝ)) * Finset.univ.sup' hne (fun i => L i / q i))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y)
    (xt xtilde : E) (hxt : xt ∈ X) (hxtilde : xtilde ∈ X)
    (G : Fin m → E →L[ℝ] ℝ)
    (hG : ∀ i, G i = (1 / (q i * (m : ℝ))) • (gradf i xt - gradf i xtilde) + gradf_full xtilde)
    (δ : Fin m → E →L[ℝ] ℝ) (hδ : ∀ i, δ i = G i - gradf_full xt),
    (∑ i, q i • δ i = 0) ∧
    (∑ i, q i * ‖δ i‖ ^ 2 ≤ 2 * LQ * (f xtilde - f xt - (gradf_full xt) (xtilde - xt))) ∧
    (∑ i, q i * ‖δ i‖ ^ 2 ≤ 4 * LQ * (Ψ xt - Ψ xstar + Ψ xtilde - Ψ xstar))) := by
  intro H
  let I : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
  have hI : ‖I‖ = 1 := by simp [I]
  let g : Fin 2 → ℝ → ℝ →L[ℝ] ℝ := fun i x => if i = 0 then x • I else -(x • I)
  have hs : ∀ (i : Fin 2) (x y : ℝ), ‖g i x - g i y‖ ≤ 1 * ‖x - y‖ := by
    intro i x y
    by_cases hi : i = 0
    · simp only [g, if_pos hi]
      erw [← sub_smul, norm_smul, hI]
      simp
    · simp only [g, if_neg hi, neg_sub_neg]
      erw [← sub_smul, norm_smul, hI, norm_sub_rev]
      simp
  have ha : ∀ x, (0 : ℝ →L[ℝ] ℝ) = (1 / (2:ℝ)) • ∑ i, g i x := by
    intro x
    simp [g, Fin.sum_univ_two]
  let G : Fin 2 → ℝ →L[ℝ] ℝ := fun i => if i = 0 then I else -I
  have hG : ∀ i, G i = (1 / ((1/2:ℝ) * 2)) • (g i 1 - g i 0) + 0 := by
    intro i
    by_cases hi : i = 0 <;> simp [G, g, hi]
  have h := @H ℝ _ _ 2 (by simp) Set.univ (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (by simp) (fun _ _ => 0) (by simp) g (fun _ => 0) ha
    (fun _ => 1) (by norm_num) hs (fun _ => 1/2) (by norm_num)
    (by norm_num [Fin.sum_univ_two]) 1 (by simp) 0 (by simp) (by simp)
    1 0 (by simp) (by simp) G hG G (by simp)
  have hh := h.2.2
  norm_num [G, Fin.sum_univ_two, hI] at hh
