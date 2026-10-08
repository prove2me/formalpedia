-- Prove2me | solution 1 for BellmanDP.Markovian.operator_estimate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:39:07.164118+00:00
-- url     : https://prove2.me/submissions/5d25f5a5-0f8f-4aea-b9ee-b3b056e0a640

import Mathlib



namespace BellmanDP.Markovian

lemma oe_integrable {N : ℕ} (t : ℝ) (ht : 0 ≤ t) (g : ℝ → ℝ) (x : ℝ → Fin N → ℝ)
    (hg : MeasureTheory.IntegrableOn g (Set.Icc 0 t)) (j : Fin N)
    (hx : ContinuousOn x (Set.Icc 0 t)) :
    IntervalIntegrable (fun s => g s * x s j) MeasureTheory.volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
  exact hg.mul_continuousOn ((continuous_apply j).comp_continuousOn hx) isCompact_Icc

theorem opest_core {N : ℕ} {P : Fin N → Type*}
    (a : (i : Fin N) → P i → ℝ → Fin N → ℝ) (b₁ b₂ : (i : Fin N) → P i → ℝ)
    (S : (i : Fin N) → Set (P i)) (t : ℝ) (ht : 0 ≤ t)
    (x y : ℝ → Fin N → ℝ) (hx : ContinuousOn x (Set.Icc 0 t)) (hy : ContinuousOn y (Set.Icc 0 t))
    (ha : ∀ (i : Fin N), ∀ q ∈ S i, ∀ j : Fin N,
      MeasureTheory.IntegrableOn (fun s => a i q s j) (Set.Icc 0 t))
    (T₁ T₂ : Fin N → ℝ)
    (hT₁ : ∀ i : Fin N, IsGreatest
      ((fun q => b₁ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * x s j) '' S i) (T₁ i))
    (hT₂ : ∀ i : Fin N, IsGreatest
      ((fun q => b₂ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * y s j) '' S i) (T₂ i)) :
    ∃ q ∈ Set.pi Set.univ S,
      ∑ i, |T₁ i - T₂ i| ≤
        ∑ i, |b₁ i (q i) - b₂ i (q i)| +
          ∫ s in (0 : ℝ)..t, (∑ i, ∑ j, |a i (q i) s j|) * ∑ j, |x s j - y s j| := by
  classical
  have hxy : ContinuousOn (fun s => ∑ j, |x s j - y s j|) (Set.Icc 0 t) := by
    refine continuousOn_finset_sum _ fun j _ => ?_
    exact (((continuous_apply j).comp_continuousOn hx).sub
      ((continuous_apply j).comp_continuousOn hy)).abs
  -- key one-row estimate
  have row : ∀ i, ∀ q ∈ S i,
      |(b₁ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * x s j) -
        (b₂ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * y s j)| ≤
      |b₁ i q - b₂ i q| + ∫ s in (0 : ℝ)..t, (∑ j, |a i q s j|) * ∑ j, |x s j - y s j| := by
    intro i q hq
    have hix : IntervalIntegrable (fun s => ∑ j, a i q s j * x s j) MeasureTheory.volume 0 t :=
      by simpa [Finset.sum_fn] using IntervalIntegrable.sum (Finset.univ) fun j _ => oe_integrable t ht _ x (ha i q hq j) j hx
    have hiy : IntervalIntegrable (fun s => ∑ j, a i q s j * y s j) MeasureTheory.volume 0 t :=
      by simpa [Finset.sum_fn] using IntervalIntegrable.sum (Finset.univ) fun j _ => oe_integrable t ht _ y (ha i q hq j) j hy
    have hg : IntervalIntegrable (fun s => (∑ j, |a i q s j|) * ∑ j, |x s j - y s j|)
        MeasureTheory.volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
      refine MeasureTheory.IntegrableOn.mul_continuousOn ?_ hxy isCompact_Icc
      exact MeasureTheory.integrable_finset_sum _ fun j _ => (ha i q hq j).abs
    have e : (b₁ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * x s j) -
        (b₂ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * y s j) =
        (b₁ i q - b₂ i q) + ∫ s in (0 : ℝ)..t,
          ((∑ j, a i q s j * x s j) - ∑ j, a i q s j * y s j) := by
      rw [intervalIntegral.integral_sub hix hiy]; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le ht
      (Filter.Eventually.of_forall fun s _ => ?_) hg
    rw [Real.norm_eq_abs, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun k => |x s k - y s k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)) (abs_nonneg _)
  -- choose q
  have hq1 := fun i => (hT₁ i).1
  have hq2 := fun i => (hT₂ i).1
  let q : (i : Fin N) → P i := fun i =>
    if T₂ i ≤ T₁ i then (hq1 i).choose else (hq2 i).choose
  have qmem : ∀ i, q i ∈ S i := by
    intro i; simp only [q]; split_ifs
    · exact (hq1 i).choose_spec.1
    · exact (hq2 i).choose_spec.1
  have hrow : ∀ i, |T₁ i - T₂ i| ≤
      |b₁ i (q i) - b₂ i (q i)| +
        ∫ s in (0 : ℝ)..t, (∑ j, |a i (q i) s j|) * ∑ j, |x s j - y s j| := by
    intro i
    have R := row i (q i) (qmem i)
    have u1 := (hT₁ i).2 ⟨q i, qmem i, rfl⟩
    have u2 := (hT₂ i).2 ⟨q i, qmem i, rfl⟩
    simp only at u1 u2
    by_cases hc : T₂ i ≤ T₁ i
    · have e1 : b₁ i (q i) + ∫ s in (0 : ℝ)..t, ∑ j, a i (q i) s j * x s j = T₁ i := by
        have := (hq1 i).choose_spec.2
        simp only [q, if_pos hc]; exact this
      rw [e1] at R
      rw [abs_of_nonneg (sub_nonneg.2 hc)]
      exact le_trans (by linarith) (le_trans (le_abs_self _) R)
    · have e2 : b₂ i (q i) + ∫ s in (0 : ℝ)..t, ∑ j, a i (q i) s j * y s j = T₂ i := by
        have := (hq2 i).choose_spec.2
        simp only [q, if_neg hc]; exact this
      rw [e2] at R
      push_neg at hc
      rw [abs_of_neg (sub_neg.2 hc)]
      exact le_trans (by linarith) (le_trans (neg_le_abs _) R)
  refine ⟨q, fun i _ => qmem i, ?_⟩
  have hint : ∀ i, IntervalIntegrable
      (fun s => (∑ j, |a i (q i) s j|) * ∑ j, |x s j - y s j|) MeasureTheory.volume 0 t := by
    intro i
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
    refine MeasureTheory.IntegrableOn.mul_continuousOn ?_ hxy isCompact_Icc
    exact MeasureTheory.integrable_finset_sum _ fun j _ => (ha i (q i) (qmem i) j).abs
  calc ∑ i, |T₁ i - T₂ i| ≤ ∑ i, (|b₁ i (q i) - b₂ i (q i)| +
        ∫ s in (0 : ℝ)..t, (∑ j, |a i (q i) s j|) * ∑ j, |x s j - y s j|) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by
      rw [Finset.sum_add_distrib, ← intervalIntegral.integral_finset_sum fun i _ => hint i]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [Finset.sum_mul]

end BellmanDP.Markovian

open BellmanDP.Markovian


theorem solution {N : ℕ} {P : Fin N → Type*}
    (a : (i : Fin N) → P i → ℝ → Fin N → ℝ) (b₁ b₂ : (i : Fin N) → P i → ℝ)
    (S : (i : Fin N) → Set (P i)) (t : ℝ) (ht : 0 ≤ t)
    (x y : ℝ → Fin N → ℝ) (hx : ContinuousOn x (Set.Icc 0 t)) (hy : ContinuousOn y (Set.Icc 0 t))
    (ha : ∀ (i : Fin N), ∀ q ∈ S i, ∀ j : Fin N,
      MeasureTheory.IntegrableOn (fun s => a i q s j) (Set.Icc 0 t))
    (T₁ T₂ : Fin N → ℝ)
    (hT₁ : ∀ i : Fin N, IsGreatest
      ((fun q => b₁ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * x s j) '' S i) (T₁ i))
    (hT₂ : ∀ i : Fin N, IsGreatest
      ((fun q => b₂ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * y s j) '' S i) (T₂ i)) :
    ∃ q ∈ Set.pi Set.univ S,
      ∑ i, |T₁ i - T₂ i| ≤
        ∑ i, |b₁ i (q i) - b₂ i (q i)| +
          ∫ s in (0 : ℝ)..t, (∑ i, ∑ j, |a i (q i) s j|) * ∑ j, |x s j - y s j| := by
  exact opest_core a b₁ b₂ S t ht x y hx hy ha T₁ T₂ hT₁ hT₂
