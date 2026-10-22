-- Prove2me | solution 1 for BreakingSample.Conservative.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:59:34.537233+00:00
-- url     : https://prove2.me/submissions/2f132856-5781-4bf1-a63a-a9ef9046be46

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Sampling
import Definitions.Def_BreakingSample_Conservative_Rule

set_option autoImplicit false
open MeasureTheory BreakingSample.Conservative

lemma bsc_maxQ_close {S A : Type} [Fintype A] [Nonempty A] (Q Qh : S → A → ℝ) (η : ℝ)
    (h : ∀ s a, |Q s a - Qh s a| ≤ η) (s : S) : |maxQ Q s - maxQ Qh s| ≤ η := by
  unfold maxQ
  rw [abs_le]
  constructor
  · -- maxQ Qh ≤ maxQ Q + η
    have : Finset.univ.sup' Finset.univ_nonempty (Qh s) ≤
        Finset.univ.sup' Finset.univ_nonempty (Q s) + η := by
      apply Finset.sup'_le
      intro a _
      have h1 := (abs_le.1 (h s a)).1
      have h2 : Q s a ≤ Finset.univ.sup' Finset.univ_nonempty (Q s) :=
        Finset.le_sup' (Q s) (Finset.mem_univ a)
      linarith
    linarith
  · have : Finset.univ.sup' Finset.univ_nonempty (Q s) ≤
        Finset.univ.sup' Finset.univ_nonempty (Qh s) + η := by
      apply Finset.sup'_le
      intro a _
      have h1 := (abs_le.1 (h s a)).2
      have h2 : Qh s a ≤ Finset.univ.sup' Finset.univ_nonempty (Qh s) :=
        Finset.le_sup' (Qh s) (Finset.mem_univ a)
      linarith
    linarith

theorem solution {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    (Qhat : S → A → ℝ) (ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 < δ) :
    BreakingSample.Perturbed.unifInterval ξ {ς : ℝ | ¬ ∀ Q : S → A → ℝ,
        (∀ s a, |Q s a - Qhat s a| ≤ ξ * δ / (8 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ))) →
        ∀ s, {a : A | maxQ Qhat s - ς < Qhat s a} = {a : A | maxQ Q s - ς < Q s a}}
      ≤ ENNReal.ofReal δ := by
  classical
  set η : ℝ := ξ * δ / (8 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ)) with hη
  have hη0 : 0 ≤ η := by positivity
  set c : S × A → ℝ := fun p => maxQ Qhat p.1 - Qhat p.1 p.2 with hc
  have hsub : {ς : ℝ | ¬ ∀ Q : S → A → ℝ, (∀ s a, |Q s a - Qhat s a| ≤ η) →
        ∀ s, {a : A | maxQ Qhat s - ς < Qhat s a} = {a : A | maxQ Q s - ς < Q s a}} ⊆
      ⋃ p ∈ (Finset.univ : Finset (S × A)), Set.Icc (c p - 2 * η) (c p + 2 * η) := by
    intro ς hς
    by_contra hcon
    apply hς
    intro Q hQ s
    have hV := bsc_maxQ_close Q Qhat η hQ s
    ext a
    simp only [Set.mem_setOf_eq]
    have hnot : ¬ (c (s, a) - 2 * η ≤ ς ∧ ς ≤ c (s, a) + 2 * η) := by
      intro hh
      apply hcon
      simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
      exact ⟨(s, a), hh⟩
    have hQa := abs_le.1 (hQ s a)
    have hVa := abs_le.1 hV
    simp only [hc] at hnot
    constructor
    · intro h1
      by_contra h2
      push Not at h2
      apply hnot
      constructor <;> linarith
    · intro h1
      by_contra h2
      push Not at h2
      apply hnot
      constructor <;> linarith
  unfold BreakingSample.Perturbed.unifInterval
  rw [ProbabilityTheory.cond_apply measurableSet_Icc]
  have hvol : volume (Set.Icc (0:ℝ) ξ) = ENNReal.ofReal ξ := by
    rw [Real.volume_Icc]; simp
  rw [hvol]
  calc (ENNReal.ofReal ξ)⁻¹ * volume (Set.Icc 0 ξ ∩ _)
      ≤ (ENNReal.ofReal ξ)⁻¹ * volume
          (⋃ p ∈ (Finset.univ : Finset (S × A)), Set.Icc (c p - 2 * η) (c p + 2 * η)) := by
        gcongr
        exact (Set.inter_subset_right).trans hsub
    _ ≤ (ENNReal.ofReal ξ)⁻¹ * ∑ p ∈ (Finset.univ : Finset (S × A)),
          volume (Set.Icc (c p - 2 * η) (c p + 2 * η)) := by
        gcongr
        exact measure_biUnion_finset_le _ _
    _ = (ENNReal.ofReal ξ)⁻¹ * ∑ p ∈ (Finset.univ : Finset (S × A)), ENNReal.ofReal (4 * η) := by
        congr 1
        apply Finset.sum_congr rfl
        intro p _
        rw [Real.volume_Icc]; congr 1; ring
    _ = ENNReal.ofReal (ξ⁻¹ * ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (4 * η))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
          ← ENNReal.ofReal_inv_of_pos hξ, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        rcases Nat.eq_zero_or_pos (Fintype.card S) with h0 | hpos
        · simp [h0, hδ.le]
        · have hS : (0:ℝ) < Fintype.card S := by exact_mod_cast hpos
          have hA : (0:ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
          rw [hη]
          field_simp
          nlinarith
