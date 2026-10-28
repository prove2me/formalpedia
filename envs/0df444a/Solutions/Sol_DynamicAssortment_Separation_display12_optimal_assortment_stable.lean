-- Prove2me | solution 1 for DynamicAssortment.Separation.display12_optimal_assortment_stable
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:08:37.87709+00:00
-- url     : https://prove2.me/submissions/556769a5-ff78-4c6e-9cfd-244411cbc548

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel

open MeasureTheory

namespace Aux_DynamicAssortment_Separation_display12

open DynamicAssortment.Separation

lemma choiceProb_congr {N : ℕ} (f : ℝ → ℝ) (ν ν' : Fin N → ℝ) (S : Finset (Fin N)) (i : Fin N)
    (h : ∀ j ∈ S, ν j = ν' j) : choiceProb f ν S i = choiceProb f ν' S i := by
  unfold choiceProb
  split_ifs with hi
  · congr 1
    funext x
    rw [Finset.prod_congr rfl (fun j hj => by rw [h j (Finset.mem_of_mem_erase hj)]), h i hi]
  · rfl

lemma cdf_nonneg (f : ℝ → ℝ) (hf : IsNoiseDensity f) (x : ℝ) : 0 ≤ noiseCDF f x :=
  setIntegral_nonneg measurableSet_Iic (fun y _ => (hf.pos y).le)

lemma choiceProb_nonneg {N : ℕ} (f : ℝ → ℝ) (hf : IsNoiseDensity f) (ν : Fin N → ℝ)
    (S : Finset (Fin N)) (i : Fin N) : 0 ≤ choiceProb f ν S i := by
  unfold choiceProb
  split_ifs
  · apply integral_nonneg
    intro x
    exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun j _ => cdf_nonneg f hf _))
      (cdf_nonneg f hf _)) (hf.pos _).le
  · exact le_rfl

lemma profit_nonneg {N : ℕ} (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ)
    (hw : ∀ i, 0 < w i) (ν : Fin N → ℝ) (S : Finset (Fin N)) : 0 ≤ profit f w ν S :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (choiceProb_nonneg f hf ν S i))

end Aux_DynamicAssortment_Separation_display12

open Aux_DynamicAssortment_Separation_display12 in
open DynamicAssortment.Separation in
theorem solution {N C : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (hopt : IsOptimalSelection f w C opt) (huniq : UniqueOptimum f w C μ (opt μ))
    (K : NNReal) (hK : 0 < K)
    (hlip : ∀ S ∈ assortments N C,
      LipschitzWith K (fun ν : Fin N → ℝ => fun i => choiceProb f ν S i)) :
    ∀ ν : Fin N → ℝ,
      normOn (opt μ ∪ opt ν) (μ - ν) <
          (2 * normOn Finset.univ w * K * C)⁻¹ * optimalityGap f w C μ (opt μ) *
            profit f w μ (opt μ) →
        opt ν = opt μ := by
  intro ν hΔ
  by_contra hne
  set A := opt μ ∪ opt ν with hA
  set Δ := normOn A (μ - ν) with hΔdef
  set W := normOn Finset.univ w with hWdef
  set rs := profit f w μ (opt μ) with hrs
  set T := opt ν with hT
  have hΔ0 : 0 ≤ Δ := NNReal.coe_nonneg _
  have hwW : ∀ i, w i ≤ W := by
    intro i
    have h1 : ‖w i‖₊ ≤ Finset.univ.sup (fun i => ‖w i‖₊) :=
      Finset.le_sup (f := fun i => ‖w i‖₊) (Finset.mem_univ i)
    have h2 : (‖w i‖₊ : ℝ) = w i := by
      rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (hw i)]
    rw [hWdef]
    unfold normOn
    rw [← h2]
    exact_mod_cast h1
  have hNpos : 0 < N := by omega
  have hWpos : 0 < W := lt_of_lt_of_le (hw ⟨0, hNpos⟩) (hwW _)
  -- perturbation bound
  have hpert : ∀ S ∈ assortments N C, S ⊆ A →
      |profit f w μ S - profit f w ν S| ≤ C * (W * (K * Δ)) := by
    intro S hS hSA
    have hcard : S.card ≤ C := (Finset.mem_filter.1 hS).2
    set ν' : Fin N → ℝ := S.piecewise ν μ with hν'
    have hcong : ∀ i, choiceProb f ν S i = choiceProb f ν' S i := fun i =>
      choiceProb_congr f ν ν' S i (fun j hj => by rw [hν', Finset.piecewise_eq_of_mem _ _ _ hj])
    have hdist : dist μ ν' ≤ Δ := by
      apply (dist_pi_le_iff hΔ0).2
      intro j
      by_cases hj : j ∈ S
      · rw [hν', Finset.piecewise_eq_of_mem _ _ _ hj, Real.dist_eq]
        have h1 : ‖(μ - ν) j‖₊ ≤ A.sup (fun i => ‖(μ - ν) i‖₊) :=
          Finset.le_sup (f := fun i => ‖(μ - ν) i‖₊) (hSA hj)
        have h2 : (‖(μ - ν) j‖₊ : ℝ) = |μ j - ν j| := by
          rw [coe_nnnorm, Real.norm_eq_abs, Pi.sub_apply]
        rw [← h2, hΔdef]
        unfold normOn
        exact_mod_cast h1
      · rw [hν', Finset.piecewise_eq_of_notMem _ _ _ hj, dist_self]
        exact hΔ0
    have hpt : ∀ i, |choiceProb f μ S i - choiceProb f ν S i| ≤ K * Δ := by
      intro i
      rw [hcong i, ← Real.dist_eq]
      have h1 := dist_le_pi_dist (fun i => choiceProb f μ S i) (fun i => choiceProb f ν' S i) i
      have h2 := (hlip S hS).dist_le_mul μ ν'
      calc dist (choiceProb f μ S i) (choiceProb f ν' S i) ≤ K * dist μ ν' := h1.trans h2
        _ ≤ K * Δ := mul_le_mul_of_nonneg_left hdist K.coe_nonneg
    unfold profit
    rw [← Finset.sum_sub_distrib]
    calc |∑ i ∈ S, (w i * choiceProb f μ S i - w i * choiceProb f ν S i)|
        ≤ ∑ i ∈ S, |w i * choiceProb f μ S i - w i * choiceProb f ν S i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ S, W * (K * Δ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [← mul_sub, abs_mul, abs_of_pos (hw i)]
          exact mul_le_mul (hwW i) (hpt i) (abs_nonneg _) hWpos.le
      _ = S.card * (W * (K * Δ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C * (W * (K * Δ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
  have hSmem := hopt.mem μ
  have hTmem := hopt.mem ν
  have hTerase : T ∈ (assortments N C).erase (opt μ) := Finset.mem_erase.2 ⟨hne, hTmem⟩
  have hgap : optimalityGap f w C μ (opt μ) ≤ (rs - profit f w μ T) / rs := by
    unfold optimalityGap
    rw [dif_pos ⟨T, hTerase⟩]
    exact Finset.inf'_le _ hTerase
  have hrs0 : 0 ≤ rs := profit_nonneg f hf w hw μ _
  have hKpos : (0 : ℝ) < K := hK
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hden : 0 < 2 * W * K * C := by positivity
  have hmain : 2 * W * K * C * Δ < optimalityGap f w C μ (opt μ) * rs := by
    have := mul_lt_mul_of_pos_left hΔ hden
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hden.ne', one_mul] at this
    linarith
  rcases eq_or_lt_of_le hrs0 with hr0 | hrpos
  · rw [← hr0, mul_zero] at hmain
    have : 0 ≤ 2 * W * K * C * Δ := by positivity
    linarith
  · have hg2 : optimalityGap f w C μ (opt μ) * rs ≤ rs - profit f w μ T := by
      have := mul_le_mul_of_nonneg_right hgap hrpos.le
      rwa [div_mul_cancel₀ _ hrpos.ne'] at this
    have h1 := hpert T hTmem (Finset.subset_union_right)
    have h2 := hpert (opt μ) hSmem (Finset.subset_union_left)
    have h3 := hopt.le_opt ν (opt μ) hSmem
    rw [abs_le] at h1 h2
    nlinarith
