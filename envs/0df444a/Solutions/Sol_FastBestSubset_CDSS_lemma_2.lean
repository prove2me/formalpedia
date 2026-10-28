-- Prove2me | solution 1 for FastBestSubset.CDSS.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:52:28.467737+00:00
-- url     : https://prove2.me/submissions/6ac0de16-712b-4f6f-b4e4-13814971b098

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting
open Filter Topology

namespace Aux_FBS2

/-- normalized objective -/
noncomputable def G (A Λ s v : ℝ) : ℝ := (v - A) ^ 2 / 2 + Λ * |v| + s ^ 2 / 2 * (if v ≠ 0 then 1 else 0)

lemma G_pos (A Λ s v : ℝ) (hv : 0 < v) : G A Λ s v = (v - A) ^ 2 / 2 + Λ * v + s ^ 2 / 2 := by
  unfold G; rw [abs_of_pos hv, if_pos hv.ne']; ring
lemma G_neg (A Λ s v : ℝ) (hv : v < 0) : G A Λ s v = (v - A) ^ 2 / 2 - Λ * v + s ^ 2 / 2 := by
  unfold G; rw [abs_of_neg hv, if_pos hv.ne]; ring
lemma G_zero (A Λ s : ℝ) : G A Λ s 0 = A ^ 2 / 2 := by unfold G; simp

-- uniqueness of the nonzero minimiser when |A| - Λ > s
lemma caseA (A Λ s : ℝ) (hΛ : 0 ≤ Λ) (hs : 0 ≤ s) (hM : |A| - Λ > s) (v : ℝ) :
    G A Λ s (Real.sign A * (|A| - Λ)) ≤ G A Λ s v ∧
      (v ≠ Real.sign A * (|A| - Λ) → G A Λ s (Real.sign A * (|A| - Λ)) < G A Λ s v) := by
  rcases lt_trichotomy A 0 with hA | hA | hA
  · rw [Real.sign_of_neg hA, abs_of_neg hA]
    rw [abs_of_neg hA] at hM
    have hu : (-1 : ℝ) * (-A - Λ) < 0 := by nlinarith
    rw [G_neg _ _ _ _ hu]
    rcases lt_trichotomy v 0 with hv | hv | hv
    · rw [G_neg _ _ _ _ hv]
      constructor
      · nlinarith [sq_nonneg (v - (-1) * (-A - Λ))]
      · intro hne
        have : v - (-1) * (-A - Λ) ≠ 0 := sub_ne_zero.mpr hne
        have := sq_pos_of_ne_zero this
        nlinarith
    · subst hv; rw [G_zero]
      constructor <;> [skip; intro _] <;> nlinarith
    · rw [G_pos _ _ _ _ hv]
      constructor <;> [skip; intro _] <;> nlinarith
  · rw [hA, abs_zero] at hM; nlinarith
  · rw [Real.sign_of_pos hA, abs_of_pos hA]
    rw [abs_of_pos hA] at hM
    have hu : (0 : ℝ) < 1 * (A - Λ) := by nlinarith
    rw [G_pos _ _ _ _ hu]
    rcases lt_trichotomy v 0 with hv | hv | hv
    · rw [G_neg _ _ _ _ hv]
      constructor <;> [skip; intro _] <;> nlinarith
    · subst hv; rw [G_zero]
      constructor <;> [skip; intro _] <;> nlinarith
    · rw [G_pos _ _ _ _ hv]
      constructor
      · nlinarith [sq_nonneg (v - 1 * (A - Λ))]
      · intro hne
        have : v - 1 * (A - Λ) ≠ 0 := sub_ne_zero.mpr hne
        have := sq_pos_of_ne_zero this
        nlinarith

lemma caseB (A Λ s : ℝ) (hΛ : 0 ≤ Λ) (hs : 0 < s) (hM : |A| - Λ < s) (v : ℝ) (hv : v ≠ 0) :
    G A Λ s 0 < G A Λ s v := by
  rw [G_zero]
  have hA1 := le_abs_self A
  have hA2 := neg_abs_le A
  rcases lt_or_gt_of_ne hv with hv | hv
  · rw [G_neg _ _ _ _ hv]
    rcases le_or_gt (|A| - Λ) 0 with hm | hm
    · nlinarith
    · nlinarith [sq_nonneg (v + (|A| - Λ))]
  · rw [G_pos _ _ _ _ hv]
    rcases le_or_gt (|A| - Λ) 0 with hm | hm
    · nlinarith
    · nlinarith [sq_nonneg (v - (|A| - Λ))]

lemma caseC (A Λ s : ℝ) (hΛ : 0 ≤ Λ) (hs : 0 < s) (hM : |A| - Λ = s) (v : ℝ) :
    G A Λ s 0 ≤ G A Λ s v ∧ G A Λ s (Real.sign A * (|A| - Λ)) = G A Λ s 0 ∧
      (v ≠ 0 → v ≠ Real.sign A * (|A| - Λ) → G A Λ s 0 < G A Λ s v) := by
  rw [G_zero]
  rcases lt_trichotomy A 0 with hA | hA | hA
  · rw [Real.sign_of_neg hA, abs_of_neg hA]
    rw [abs_of_neg hA] at hM
    have hu : (-1 : ℝ) * (-A - Λ) < 0 := by nlinarith
    rw [G_neg _ _ _ _ hu]
    refine ⟨?_, by nlinarith, fun hv0 hvu => ?_⟩
    · rcases lt_trichotomy v 0 with hv | hv | hv
      · rw [G_neg _ _ _ _ hv]; nlinarith [sq_nonneg (v - (A + Λ))]
      · subst hv; rw [G_zero]
      · rw [G_pos _ _ _ _ hv]; nlinarith
    · rcases lt_or_gt_of_ne hv0 with hv | hv
      · rw [G_neg _ _ _ _ hv]
        have : v - (-1) * (-A - Λ) ≠ 0 := sub_ne_zero.mpr hvu
        have := sq_pos_of_ne_zero this
        nlinarith
      · rw [G_pos _ _ _ _ hv]; nlinarith
  · rw [hA, abs_zero] at hM; nlinarith
  · rw [Real.sign_of_pos hA, abs_of_pos hA]
    rw [abs_of_pos hA] at hM
    have hu : (0 : ℝ) < 1 * (A - Λ) := by nlinarith
    rw [G_pos _ _ _ _ hu]
    refine ⟨?_, by nlinarith, fun hv0 hvu => ?_⟩
    · rcases lt_trichotomy v 0 with hv | hv | hv
      · rw [G_neg _ _ _ _ hv]; nlinarith
      · subst hv; rw [G_zero]
      · rw [G_pos _ _ _ _ hv]; nlinarith [sq_nonneg (v - (A - Λ))]
    · rcases lt_or_gt_of_ne hv0 with hv | hv
      · rw [G_neg _ _ _ _ hv]; nlinarith
      · rw [G_pos _ _ _ _ hv]
        have : v - 1 * (A - Λ) ≠ 0 := sub_ne_zero.mpr hvu
        have := sq_pos_of_ne_zero this
        nlinarith

end Aux_FBS2

open FastBestSubset.CDSS in
theorem solution (a lam0 lam1 lam2 : ℝ) (hlam0 : 0 < lam0) (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2) :
    ((|a| - lam1) / (1 + 2 * lam2) > Real.sqrt (2 * lam0 / (1 + 2 * lam2)) →
        Ttilde a lam0 lam1 lam2 = {Real.sign a * (|a| - lam1) / (1 + 2 * lam2)}) ∧
    ((|a| - lam1) / (1 + 2 * lam2) < Real.sqrt (2 * lam0 / (1 + 2 * lam2)) →
        Ttilde a lam0 lam1 lam2 = {0}) ∧
    ((|a| - lam1) / (1 + 2 * lam2) = Real.sqrt (2 * lam0 / (1 + 2 * lam2)) →
        Ttilde a lam0 lam1 lam2 = {0, Real.sign a * (|a| - lam1) / (1 + 2 * lam2)}) := by
  set c := 1 + 2 * lam2 with hc
  have hcpos : 0 < c := by linarith
  set s := Real.sqrt (2 * lam0 / c) with hs
  have hs2 : s ^ 2 = 2 * lam0 / c := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  set A := a / c with hA
  set Λ := lam1 / c with hΛ
  have hΛ0 : 0 ≤ Λ := div_nonneg hlam1 hcpos.le
  have hgG : ∀ v, gScalar a lam0 lam1 lam2 v = c * Aux_FBS2.G A Λ s v := by
    intro v
    unfold gScalar Aux_FBS2.G
    rw [hs2, ← hc, hA, hΛ]
    split_ifs <;> field_simp <;> ring
  have hM : (|a| - lam1) / c = |A| - Λ := by
    rw [hA, hΛ, abs_div, abs_of_pos hcpos]; ring
  have hsignA : Real.sign A = Real.sign a := by
    rw [hA]
    rcases lt_trichotomy a 0 with h | h | h
    · rw [Real.sign_of_neg h, Real.sign_of_neg (div_neg_of_neg_of_pos h hcpos)]
    · rw [h, zero_div]
    · rw [Real.sign_of_pos h, Real.sign_of_pos (div_pos h hcpos)]
  have hustar : Real.sign a * (|a| - lam1) / c = Real.sign A * (|A| - Λ) := by
    rw [mul_div_assoc, hM, hsignA]
  have hmem : ∀ u, u ∈ Ttilde a lam0 lam1 lam2 ↔ ∀ v, Aux_FBS2.G A Λ s u ≤ Aux_FBS2.G A Λ s v := by
    intro u
    unfold Ttilde
    simp only [Set.mem_setOf_eq, hgG]
    exact forall_congr' (fun v => mul_le_mul_iff_of_pos_left hcpos)
  rw [hM, hustar]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · ext u
    rw [hmem, Set.mem_singleton_iff]
    constructor
    · intro hu
      by_contra hne
      have := (Aux_FBS2.caseA A Λ s hΛ0 hspos.le h u).2 hne
      linarith [hu (Real.sign A * (|A| - Λ))]
    · rintro rfl v
      exact (Aux_FBS2.caseA A Λ s hΛ0 hspos.le h v).1
  · ext u
    rw [hmem, Set.mem_singleton_iff]
    constructor
    · intro hu
      by_contra hne
      have := Aux_FBS2.caseB A Λ s hΛ0 hspos h u hne
      linarith [hu 0]
    · rintro rfl v
      by_cases hv : v = 0
      · rw [hv]
      · exact (Aux_FBS2.caseB A Λ s hΛ0 hspos h v hv).le
  · ext u
    rw [hmem, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hu
      by_contra hne
      push_neg at hne
      have := (Aux_FBS2.caseC A Λ s hΛ0 hspos h u).2.2 hne.1 hne.2
      linarith [hu 0]
    · rintro (rfl | rfl) v
      · exact (Aux_FBS2.caseC A Λ s hΛ0 hspos h v).1
      · rw [(Aux_FBS2.caseC A Λ s hΛ0 hspos h v).2.1]
        exact (Aux_FBS2.caseC A Λ s hΛ0 hspos h v).1
