-- Prove2me | solution 1 for BwSC.LowerBound.corollary_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:09:22.950333+00:00
-- url     : https://prove2.me/submissions/f78b3f3e-4c1d-4742-900b-0b83a59b99af

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof
import Theorems.Thm_BwSC_LowerBound_lemma_6
import Theorems.Thm_BwSC_LowerBound_lemma_7

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.Cor4Aux

lemma rIdx_le {S K : ℕ} (hK : 1 < K) : rIdx S K ≤ (K : ℤ) - 2 := by
  unfold rIdx qIdx
  by_cases hS : S = 0
  · subst hS; simp; omega
  · rw [if_neg hS]
    have hdm := Nat.div_add_mod (S - 1) (K - 1)
    have hlt := Nat.mod_lt (S - 1) (by omega : K - 1 > 0)
    have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
    have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
    have e : (S : ℤ) - 1 - (((S - 1) / (K - 1) : ℕ) : ℤ) * ((K : ℤ) - 1) =
        (((S - 1) % (K - 1) : ℕ) : ℤ) := by
      rw [← hS1, ← hK1]; push_cast; zify at hdm; linarith
    rw [e]
    zify at hlt; push_cast at hlt ⊢; omega

/-- `S = r + 1 + q (K - 1)` (definition of `r(S,K)`). -/
lemma S_eq (S K : ℕ) :
    (S : ℝ) = (rIdx S K : ℝ) + 1 + (qIdx S K : ℝ) * ((K : ℝ) - 1) := by
  unfold rIdx; push_cast; ring

/-- `⌈S/(q+1)⌉ ≤ (S + q)/(q+1)`. -/
lemma ceil_le (S q : ℕ) :
    ((⌈(S : ℝ) / ((q : ℝ) + 1)⌉ : ℤ) : ℝ) ≤ ((S : ℝ) + q) / ((q : ℝ) + 1) := by
  have hdm := Nat.div_add_mod (S + q) (q + 1)
  have hmod := Nat.mod_lt (S + q) (by omega : q + 1 > 0)
  generalize (S + q) / (q + 1) = c at hdm
  generalize (S + q) % (q + 1) = d at hdm hmod
  generalize hP : (q + 1) * c = P at hdm
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have h1 : (S : ℝ) / ((q : ℝ) + 1) ≤ (c : ℝ) := by
    rw [div_le_iff₀ hq1]
    have : S ≤ (q + 1) * c := by omega
    have : (S : ℝ) ≤ ((q : ℝ) + 1) * c := by exact_mod_cast this
    linarith
  have h2 : ⌈(S : ℝ) / ((q : ℝ) + 1)⌉ ≤ (c : ℤ) := Int.ceil_le.mpr (by exact_mod_cast h1)
  have h3 : (c : ℝ) ≤ ((S : ℝ) + q) / ((q : ℝ) + 1) := by
    rw [le_div_iff₀ hq1]
    have : (q + 1) * c ≤ S + q := by omega
    have : ((q : ℝ) + 1) * c ≤ (S : ℝ) + q := by exact_mod_cast this
    linarith
  have h4 : ((⌈(S : ℝ) / ((q : ℝ) + 1)⌉ : ℤ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast h2
  linarith

end BwSC.LowerBound.Cor4Aux

open BwSC.LowerBound BwSC.LowerBound.Cor4Aux in
theorem solution {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (μvec : Fin K → ℝ) :
    ((K : ℝ) - (rIdx S K : ℝ)) / (2 * ((qIdx S K : ℝ) + 2) ^ 2 * K) ≤
        1 / (((qIdx S K : ℝ) + 2) * K) *
          ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
            ((banditMeasure (gaussianBandit μvec) π T) (E1 S K T j k)).toReal ∧
      1 / (2 * ((qIdx S K : ℝ) + 2) ^ 2) ≤
        1 / (((qIdx S K : ℝ) + 2) * K) *
          ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
            ((banditMeasure (gaussianBandit μvec) π T) (E2 S K T j k)).toReal := by
  have h6 := lemma_6 hK hT π hπ μvec
  have h7 := lemma_7 hK hT π hπ μvec
  set q : ℝ := (qIdx S K : ℝ) with hq
  set r : ℝ := (rIdx S K : ℝ) with hr
  have hq0 : 0 ≤ q := by positivity
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hrK : r ≤ (K : ℝ) - 2 := by rw [hr]; exact_mod_cast rIdx_le (S := S) hK
  have hS := S_eq S K
  rw [← hq, ← hr] at hS
  have hceil := ceil_le S (qIdx S K)
  rw [← hq] at hceil
  have hfloor : ((⌊(S : ℝ) / (q + 2)⌋ : ℤ) : ℝ) ≤ (S : ℝ) / (q + 2) := Int.floor_le _
  have hn : 0 < q + 2 := by linarith
  have hnK : 0 < (q + 2) * K := by positivity
  constructor
  · set X := ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
        ((banditMeasure (gaussianBandit μvec) π T) (E1 S K T j k)).toReal
    -- K - ⌈S/(q+1)⌉ ≥ (K - r - 1)/(q+1) ≥ (K - r)/(2(q+2))
    have hA : ((K : ℝ) - r) / (2 * (q + 2)) ≤ X := by
      have e1 : ((K : ℝ) - r) / (2 * (q + 2)) ≤ (K : ℝ) - ((S : ℝ) + q) / (q + 1) := by
        rw [hS, div_le_iff₀ (by positivity)]
        have : (K : ℝ) - (r + 1 + q * ((K : ℝ) - 1) + q) / (q + 1) = ((K : ℝ) - r - 1) / (q + 1) := by
          field_simp; ring
        rw [this, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hA
    have : 1 / ((q + 2) * K) * X * (2 * (q + 2) ^ 2 * K) = 2 * (q + 2) * X := by
      field_simp
    rw [this]; linarith
  · set Y := ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
        ((banditMeasure (gaussianBandit μvec) π T) (E2 S K T j k)).toReal
    have hB : (K : ℝ) / (2 * (q + 2)) ≤ Y := by
      have e1 : (K : ℝ) / (2 * (q + 2)) ≤ (K : ℝ) - 1 - (S : ℝ) / (q + 2) := by
        rw [hS, div_le_iff₀ (by positivity)]
        have : (K : ℝ) - 1 - (r + 1 + q * ((K : ℝ) - 1)) / (q + 2) =
            (2 * ((K : ℝ) - 1) - r - 1) / (q + 2) := by
          field_simp; ring
        rw [this, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    rw [div_le_iff₀ (by positivity)]
    have : 1 / ((q + 2) * K) * Y * (2 * (q + 2) ^ 2) = 2 * (q + 2) / K * Y := by
      field_simp
    rw [this, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hB
    linarith
