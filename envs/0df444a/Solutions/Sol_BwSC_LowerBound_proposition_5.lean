-- Prove2me | solution 1 for BwSC.LowerBound.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:56:20.359623+00:00
-- url     : https://prove2.me/submissions/20b0c7da-ec84-4efd-b617-0146a71b994d

import Mathlib
import Theorems.Thm_ExploreFirst_FundIneq_lemma_1
import Theorems.Thm_ExploreFirst_Collective_lemma_6
import Theorems.Thm_BwSC_LowerBound_lemma_5_reverse

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

universe u

/-- Averaging step: per-index bounds `(q_i - p_i)² ≤ 2 q_i D_i` (when `p_i < q_i`) give
`q̄ - √(2 q̄ D̄) ≤ p̄` by Cauchy–Schwarz. -/
lemma avg_bound {N : ℕ} (hN : 0 < N) (p q D : Fin N → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hD : ∀ i, 0 ≤ D i) (hp : ∀ i, 0 ≤ p i) (h : ∀ i, p i < q i → (p i - q i) ^ 2 / (2 * q i) ≤ D i) :
    (1 / (N : ℝ)) * ∑ i, q i -
        Real.sqrt (2 * ((1 / (N : ℝ)) * ∑ i, q i) * ((1 / (N : ℝ)) * ∑ i, D i))
      ≤ (1 / (N : ℝ)) * ∑ i, p i := by
  set a : Fin N → ℝ := fun i => max (q i - p i) 0 with ha
  have hai : ∀ i, a i ≤ Real.sqrt (2 * q i) * Real.sqrt (D i) := by
    intro i
    simp only [ha]
    rcases lt_or_ge (p i) (q i) with hlt | hge
    · rw [max_eq_left (by linarith), ← Real.sqrt_mul (by linarith [hq i])]
      apply Real.le_sqrt_of_sq_le
      have hqi : 0 < q i := by linarith [hp i]
      have := h i hlt
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
    · rw [max_eq_right (by linarith)]
      positivity
  have hsum : ∑ i, (q i - p i) ≤ Real.sqrt (∑ i, 2 * q i) * Real.sqrt (∑ i, D i) := by
    calc ∑ i, (q i - p i) ≤ ∑ i, a i := Finset.sum_le_sum (fun i _ => le_max_left _ _)
      _ ≤ ∑ i, Real.sqrt (2 * q i) * Real.sqrt (D i) := Finset.sum_le_sum (fun i _ => hai i)
      _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _ (fun i => by linarith [hq i]) hD
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.sqrt (2 * ((1 / (N : ℝ)) * ∑ i, q i) * ((1 / (N : ℝ)) * ∑ i, D i)) =
      (1 / (N : ℝ)) * (Real.sqrt (∑ i, 2 * q i) * Real.sqrt (∑ i, D i)) := by
    rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => by linarith [hq i]))]
    have : 2 * ((1 / (N : ℝ)) * ∑ i, q i) * ((1 / (N : ℝ)) * ∑ i, D i) =
        (1 / (N : ℝ)) ^ 2 * ((∑ i, 2 * q i) * ∑ i, D i) := by
      rw [← Finset.mul_sum]; ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [key]
  have : (1 / (N : ℝ)) * ∑ i, q i - (1 / (N : ℝ)) * ∑ i, p i = (1 / (N : ℝ)) * ∑ i, (q i - p i) := by
    rw [Finset.sum_sub_distrib]; ring
  have h2 := mul_le_mul_of_nonneg_left hsum (by positivity : (0:ℝ) ≤ 1 / (N : ℝ))
  linarith

/-- Per-index bound from the data-processing inequality for Bernoulli divergences. -/
lemma per_index {Ω : Type u} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (E : Set Ω) (hE : MeasurableSet E) :
    ((Q E).toReal ≠ 0 → (P E).toReal < (Q E).toReal → klDiv P Q ≠ ∞ →
      ((P E).toReal - (Q E).toReal) ^ 2 / (2 * (Q E).toReal) ≤ (klDiv P Q).toReal) ∧
    ((P E).toReal < (Q E).toReal → klDiv Q P ≠ ∞ →
      ((P E).toReal - (Q E).toReal) ^ 2 / (2 * (Q E).toReal) ≤ (klDiv Q P).toReal) := by
  have hZm : Measurable (E.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hE
  have hZ01 : ∀ γ, E.indicator (fun _ => (1 : ℝ)) γ ∈ Set.Icc (0 : ℝ) 1 := by
    intro γ; by_cases hγ : γ ∈ E <;> simp [Set.indicator, hγ]
  have iP : ∫ γ, E.indicator (fun _ => (1 : ℝ)) γ ∂P = (P E).toReal := by
    rw [integral_indicator_const _ hE]; simp [Measure.real]
  have iQ : ∫ γ, E.indicator (fun _ => (1 : ℝ)) γ ∂Q = (Q E).toReal := by
    rw [integral_indicator_const _ hE]; simp [Measure.real]
  have h1 := ExploreFirst.FundIneq.lemma_1 P Q _ hZm hZ01
  have h2 := ExploreFirst.FundIneq.lemma_1 Q P _ hZm hZ01
  rw [iP, iQ] at h1 h2
  have hp0 : 0 ≤ (P E).toReal := ENNReal.toReal_nonneg
  have hq1 : (Q E).toReal ≤ 1 := by
    have : Q E ≤ 1 := prob_le_one
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  refine ⟨fun _ hlt hfin => ?_, fun hlt hfin => ?_⟩
  · obtain ⟨l1, l2⟩ := ExploreFirst.Collective.lemma_6 _ _ hp0 hlt hq1
    have : ENNReal.ofReal (((P E).toReal - (Q E).toReal) ^ 2 / (2 * (Q E).toReal)) ≤ klDiv P Q :=
      ((ENNReal.ofReal_le_ofReal l2).trans l1).trans h1
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp this
  · have l := BwSC.LowerBound.lemma_5_reverse _ _ hp0 hlt.le hq1
    have : ENNReal.ofReal (((P E).toReal - (Q E).toReal) ^ 2 / (2 * (Q E).toReal)) ≤ klDiv Q P :=
      l.trans h2
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp this

theorem solution {N : ℕ} (hN : 0 < N) {Ω : Fin N → Type u}
    [∀ i, MeasurableSpace (Ω i)] (P Q : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]
    (E : ∀ i, Set (Ω i)) (hE : ∀ i, MeasurableSet (E i)) :
    ((∀ i, klDiv (P i) (Q i) ≠ ∞) →
      (1 / (N : ℝ)) * ∑ i, (Q i (E i)).toReal -
          Real.sqrt (2 * ((1 / (N : ℝ)) * ∑ i, (Q i (E i)).toReal) *
            ((1 / (N : ℝ)) * ∑ i, (klDiv (P i) (Q i)).toReal))
        ≤ (1 / (N : ℝ)) * ∑ i, (P i (E i)).toReal) ∧
    ((∀ i, klDiv (Q i) (P i) ≠ ∞) →
      (1 / (N : ℝ)) * ∑ i, (Q i (E i)).toReal -
          Real.sqrt (2 * ((1 / (N : ℝ)) * ∑ i, (Q i (E i)).toReal) *
            ((1 / (N : ℝ)) * ∑ i, (klDiv (Q i) (P i)).toReal))
        ≤ (1 / (N : ℝ)) * ∑ i, (P i (E i)).toReal) := by
  refine ⟨fun hfin => ?_, fun hfin => ?_⟩
  · refine avg_bound hN _ _ _ (fun i => ENNReal.toReal_nonneg) (fun i => ENNReal.toReal_nonneg) (fun i => ENNReal.toReal_nonneg) ?_
    intro i hlt
    have hq0 : (Q i (E i)).toReal ≠ 0 := by
      have : (0 : ℝ) ≤ (P i (E i)).toReal := ENNReal.toReal_nonneg
      linarith
    exact (per_index (P i) (Q i) (E i) (hE i)).1 hq0 hlt (hfin i)
  · refine avg_bound hN _ _ _ (fun i => ENNReal.toReal_nonneg) (fun i => ENNReal.toReal_nonneg) (fun i => ENNReal.toReal_nonneg) ?_
    intro i hlt
    exact (per_index (P i) (Q i) (E i) (hE i)).2 hlt (hfin i)
