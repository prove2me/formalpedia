-- Prove2me | solution 1 for DynamicAssortment.Separation.display11_profit_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:48:47.193834+00:00
-- url     : https://prove2.me/submissions/41463f72-86b9-40da-afef-334150623404

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel

open DynamicAssortment.Separation in
theorem solution {N C : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (K : NNReal) (hK : 0 < K)
    (hlip : ∀ S ∈ assortments N C,
      LipschitzWith K (fun ν : Fin N → ℝ => fun i => choiceProb f ν S i)) :
    ∀ S ∈ assortments N C, ∀ ν : Fin N → ℝ,
      |profit f w μ S - profit f w ν S| ≤ normOn Finset.univ w * K * C * normOn S (μ - ν) := by
  intro S hS ν
  obtain ⟨ν', hS', hN'⟩ : ∃ ν' : Fin N → ℝ, (∀ j ∈ S, ν' j = ν j) ∧ (∀ j ∉ S, ν' j = μ j) :=
    ⟨fun j => if j ∈ S then ν j else μ j, fun j hj => if_pos hj, fun j hj => if_neg hj⟩
  have hcp : ∀ i, choiceProb f ν' S i = choiceProb f ν S i := by
    intro i
    unfold choiceProb
    split_ifs with hi
    · have h1 : ∀ x, ∏ j ∈ S.erase i, noiseCDF f (x - ν' j) = ∏ j ∈ S.erase i, noiseCDF f (x - ν j) :=
        fun x => Finset.prod_congr rfl (fun j hj => by rw [hS' j (Finset.mem_of_mem_erase hj)])
      simp only [h1, hS' i hi]
    · rfl
  have hW : normOn Finset.univ w = ‖w‖ := rfl
  set n := normOn S (μ - ν) with hn
  have hn0 : 0 ≤ n := NNReal.coe_nonneg _
  have hdist : dist μ ν' ≤ n := by
    rw [dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg hn0).2 fun j => ?_
    by_cases hj : j ∈ S
    · rw [Pi.sub_apply, hS' j hj]
      have : ‖(μ - ν) j‖₊ ≤ S.sup fun i => ‖(μ - ν) i‖₊ :=
        Finset.le_sup (f := fun i => ‖(μ - ν) i‖₊) hj
      have h2 := NNReal.coe_le_coe.2 this
      rw [coe_nnnorm, Pi.sub_apply] at h2
      exact h2
    · rw [Pi.sub_apply, hN' j hj, sub_self, norm_zero]; exact hn0
  have hL := (hlip S hS).dist_le_mul μ ν'
  have hd : ∀ i, |choiceProb f μ S i - choiceProb f ν' S i| ≤ K * n := by
    intro i
    have := dist_le_pi_dist (fun i => choiceProb f μ S i) (fun i => choiceProb f ν' S i) i
    rw [Real.dist_eq] at this
    calc _ ≤ _ := this
      _ ≤ K * dist μ ν' := hL
      _ ≤ K * n := mul_le_mul_of_nonneg_left hdist K.coe_nonneg
  have hcard : (S.card : ℝ) ≤ C := by
    have := (Finset.mem_filter.1 hS).2; exact_mod_cast this
  have hdiff : profit f w μ S - profit f w ν S =
      ∑ i ∈ S, w i * (choiceProb f μ S i - choiceProb f ν' S i) := by
    unfold profit
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcp i]; ring
  rw [hdiff]
  have hwn : ∀ i, |w i| ≤ ‖w‖ := fun i => by
    have := norm_le_pi_norm w i; rwa [Real.norm_eq_abs] at this
  calc |∑ i ∈ S, w i * (choiceProb f μ S i - choiceProb f ν' S i)|
      ≤ ∑ i ∈ S, |w i * (choiceProb f μ S i - choiceProb f ν' S i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ‖w‖ * (K * n) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hwn i) (hd i) (abs_nonneg _) (norm_nonneg _)
    _ = S.card * (‖w‖ * (K * n)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * (‖w‖ * (K * n)) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (norm_nonneg _) (mul_nonneg K.coe_nonneg hn0))
    _ = normOn Finset.univ w * K * C * n := by rw [hW]; ring
