-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_killed_cutoff_liminf_ito_to_ruin_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:05:43.717971+00:00
-- url     : https://prove2.me/submissions/ee44225d-8d74-401c-8844-bef97631a107

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_real_payment_stieltjes_zero_cap_spatial_eventual_cover
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_killed_real_zero_cap_spatial_support_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
/-- The true killed finite-horizon zero/cap and shrinking interior cash budgets pass to exact ruin cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x T : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hStrategy : IsDividendStrategy 𝓕 D)
    (hxc : ENNReal.ofReal x ≤ C)
    (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞)
    (hlower : Filter.Tendsto lower Filter.atTop (𝓝 0))
    (hupper : Filter.Tendsto upper Filter.atTop (𝓝 C))
    (budget : ℝ≥0∞)
    (hBudgetLiminf : Filter.liminf (fun n : ℕ =>
      (∫⁻ ω, (∫⁻ t in
        {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
          (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)} ∪
        {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
          lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P)) Filter.atTop ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  let B : Ω → Set ℝ := fun ω =>
    {t | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
      (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
        ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)}
  let I : ℕ → Ω → Set ℝ := fun n ω =>
    {t | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
      lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
        ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n}
  have hm (n : ℕ) :=
    avram_wave7_19_original_killed_real_zero_cap_spatial_support_joint_measurable
      X x T C D hStrategy lower upper n
  have hbm : ∀ ω, MeasurableSet (B ω) := by
    intro ω
    exact (measurable_id.prodMk measurable_const) (hm 0).1
  have him : ∀ n ω, MeasurableSet (I n ω) := by
    intro n ω
    exact (measurable_id.prodMk measurable_const) (hm n).2
  have hj : ∀ n : ℕ,
      MeasurableSet {p : ℝ × Ω | p.1 ∈ B p.2 ∪ I n p.2} := by
    intro n
    exact (hm n).1.union (hm n).2
  have hev : ∀ᵐ ω ∂P,
      ∀ t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ∀ᶠ n : ℕ in Filter.atTop, t ∈ B ω ∪ I n ω := by
    apply Filter.Eventually.of_forall
    intro ω t ht
    have hs :=
      avram_wave7_19_original_real_payment_stieltjes_zero_cap_spatial_eventual_cover
        X x C D hD hxc T lower upper hlower hupper ω t ht
    filter_upwards [hs] with n hn
    rcases hn with hz | hc | hi
    · exact Or.inl ⟨ht.1, ht.2, Or.inl hz⟩
    · exact Or.inl ⟨ht.1, ht.2, Or.inr hc⟩
    · exact Or.inr ⟨ht.1, ht.2, hi.1, hi.2⟩
  exact avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
    X q x T D hStrategy B I hbm him hj hev budget hBudgetLiminf
