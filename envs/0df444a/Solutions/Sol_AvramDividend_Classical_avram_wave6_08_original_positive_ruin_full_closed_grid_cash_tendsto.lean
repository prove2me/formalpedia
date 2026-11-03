-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_ruin_full_closed_grid_cash_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:02:33.104436+00:00
-- url     : https://prove2.me/submissions/6dd98c44-781d-4fb7-9d09-c0b2b1e18dce

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_discounted_preterminal_cash_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- True closed grid cash converges to positive-ruin paid cash, retaining
the t = 0 right atom and excluding the positive ruin-time right atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < τ)
    (hlim : Tendsto u atTop (𝓝 τ)) :
    Tendsto (fun n => ∫⁻ t in Icc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let initial : ℝ≥0∞ := ∫⁻ t in ({(0 : ℝ)} : Set ℝ), f t ∂μ
  let preCash : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ t in Ioc (0 : ℝ) (u n : ℝ), f t ∂μ
  let closed : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ t in Icc (0 : ℝ) (u n : ℝ), f t ∂μ
  let full : ℝ≥0∞ := ∫⁻ t in Ioo (0 : ℝ) (τ : ℝ), f t ∂μ
  let paid : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ), f t ∂μ
  have hpre : Tendsto preCash atTop (𝓝 full) :=
    avram_wave6_08_original_positive_ruin_discounted_preterminal_cash_tendsto
      D hD ω q hq τ hτ u hu hlim
  have hpaid : paid = initial + full :=
    avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left
      D hD ω q τ hτ
  have hcell (n : ℕ) : closed n = initial + preCash n := by
    have hset : Icc (0 : ℝ) (u n : ℝ) =
        ({(0 : ℝ)} : Set ℝ) ∪ Ioc (0 : ℝ) (u n : ℝ) := by
      ext t
      simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioc]
      constructor
      · rintro ⟨ht0, htu⟩
        by_cases hz : t = 0
        · exact Or.inl hz
        · exact Or.inr ⟨lt_of_le_of_ne ht0 (Ne.symm hz), htu⟩
      · rintro (rfl | ⟨ht0, htu⟩)
        · exact ⟨le_refl _, NNReal.coe_nonneg (u n)⟩
        · exact ⟨le_of_lt ht0, htu⟩
    have hdisj : Disjoint ({(0 : ℝ)} : Set ℝ)
        (Ioc (0 : ℝ) (u n : ℝ)) := by
      refine Set.disjoint_left.mpr ?_
      intro t hzero ht
      simp only [mem_singleton_iff] at hzero
      subst t
      exact (lt_irrefl (0 : ℝ)) ht.1
    change (∫⁻ t in Icc (0 : ℝ) (u n : ℝ), f t ∂μ) =
      (∫⁻ t in ({(0 : ℝ)} : Set ℝ), f t ∂μ) +
        (∫⁻ t in Ioc (0 : ℝ) (u n : ℝ), f t ∂μ)
    rw [hset]
    exact lintegral_union measurableSet_Ioc hdisj
  have hlimcash : Tendsto (fun n => initial + preCash n)
      atTop (𝓝 (initial + full)) :=
    tendsto_const_nhds.add hpre
  change Tendsto closed atTop (𝓝 paid)
  rw [hpaid]
  exact hlimcash.congr' (Filter.Eventually.of_forall (fun n => (hcell n).symm))
