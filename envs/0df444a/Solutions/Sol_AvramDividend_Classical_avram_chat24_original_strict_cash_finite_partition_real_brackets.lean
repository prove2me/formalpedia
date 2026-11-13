-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_strict_cash_finite_partition_real_brackets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:47:38.463246+00:00
-- url     : https://prove2.me/submissions/36872f2d-96e8-48f7-a90d-dd395de778ad

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_Ico_partition_bracket
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
open Finset

lemma lintegral_monotone_Ico_partition
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    (∫⁻ t in Ico (u 0) (u n), f t ∂μ) =
      ∑ i ∈ range n, ∫⁻ t in Ico (u i) (u (i + 1)), f t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hun : Ico (u 0) (u (n + 1)) = Ico (u 0) (u n) ∪ Ico (u n) (u (n + 1)) := by
      ext t
      simp only [Set.mem_Ico, Set.mem_union]
      constructor
      · intro ht
        by_cases hn : t < u n
        · exact Or.inl ⟨ht.1, hn⟩
        · exact Or.inr ⟨le_of_not_gt hn, ht.2⟩
      · rintro (ht | ht)
        · exact ⟨ht.1, lt_of_lt_of_le ht.2 (hu (Nat.le_succ n))⟩
        · exact ⟨le_trans (hu (Nat.zero_le n)) ht.1, ht.2⟩
    have hd : Disjoint (Ico (u 0) (u n)) (Ico (u n) (u (n + 1))) :=
      Set.disjoint_left.mpr (fun t ht hs => (not_lt_of_ge hs.1) ht.2)
    rw [hun, lintegral_union measurableSet_Ico hd, ih, sum_range_succ]

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    let cash : ℝ≥0∞ := ∫⁻ t in Ico (u 0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
    cash ≠ ⊤ ∧
      (∑ i ∈ Finset.range n, Real.exp (-(q * (u (i + 1) : ℝ))) *
        (D (u (i + 1)) ω - D (u i) ω)) ≤ cash.toReal ∧
      cash.toReal ≤ (∑ i ∈ Finset.range n, Real.exp (-(q * (u i : ℝ))) *
        (D (u (i + 1)) ω - D (u i) ω)) := by
  classical
  intro cash
  let c : ℕ → ℝ≥0∞ := fun i => ∫⁻ t in Ico (u i : ℝ) (u (i + 1) : ℝ),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hc (i : ℕ) : c i ≠ ⊤ ∧
      Real.exp (-(q * (u (i + 1) : ℝ))) * (D (u (i + 1)) ω - D (u i) ω) ≤ (c i).toReal ∧
      (c i).toReal ≤ Real.exp (-(q * (u i : ℝ))) * (D (u (i + 1)) ω - D (u i) ω) := by
    have hb := discounted_dividendMeasure_Ico_partition_bracket D hD ω q hq (u i) (u (i + 1))
    have hd : 0 ≤ D (u (i + 1)) ω - D (u i) ω :=
      sub_nonneg.mpr (hD.2.1 ω (hu (Nat.le_succ i)))
    have hf : c i ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hb.2 ENNReal.ofReal_lt_top)
    refine ⟨hf, ?_, ?_⟩
    · simpa only [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hd)] using
        ENNReal.toReal_mono hf hb.1
    · simpa only [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hd)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hb.2
  have hp : cash = ∑ i ∈ range n, c i := by
    exact lintegral_monotone_Ico_partition (dividendMeasure D ω)
      (fun t => ENNReal.ofReal (Real.exp (-(q * t))))
      (fun i => (u i : ℝ)) (fun i j hij => by exact_mod_cast hu hij) n
  have hr : cash.toReal = ∑ i ∈ range n, (c i).toReal := by
    rw [hp]
    exact ENNReal.toReal_sum (fun i hi => (hc i).1)
  have hb := discounted_dividendMeasure_Ico_partition_bracket D hD ω q hq (u 0) (u n)
  refine ⟨ne_of_lt (lt_of_le_of_lt hb.2 ENNReal.ofReal_lt_top), ?_, ?_⟩
  · rw [hr]
    exact Finset.sum_le_sum (fun i hi => (hc i).2.1)
  · rw [hr]
    exact Finset.sum_le_sum (fun i hi => (hc i).2.2)

