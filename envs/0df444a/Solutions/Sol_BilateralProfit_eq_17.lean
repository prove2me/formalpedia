-- Prove2me | solution 1 for BilateralProfit.eq_17
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T13:32:50.287775+00:00
-- url     : https://prove2.me/submissions/2f56df04-7a01-490b-9ff3-38f45c09c847

import Mathlib
import Definitions.Def_BilateralProfit_SellerTree

open MeasureTheory

namespace BilateralProfit.Eq17

theorem trade_rectangle (μ : Measure (ℝ × ℝ)) (p q : ℝ) :
    Ptrade μ (p, q) = μ.real (Set.Iic p ×ˢ Set.Ici q) := rfl

theorem seller_split (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (l r q : ℝ) (hlr : l ≤ r) :
    Ptrade μ (r, q) = Ptrade μ (l, q) + μ.real (Set.Ioc l r ×ˢ Set.Ici q) := by
  rw [trade_rectangle, trade_rectangle]
  have hset : Set.Iic r ×ˢ Set.Ici q =
      (Set.Iic l ×ˢ Set.Ici q) ∪ (Set.Ioc l r ×ˢ Set.Ici q) := by
    ext v
    simp only [Set.mem_prod, Set.mem_Iic, Set.mem_Ici, Set.mem_union, Set.mem_Ioc]
    constructor
    · rintro ⟨hv, hb⟩
      by_cases h : v.1 ≤ l
      · exact Or.inl ⟨h, hb⟩
      · exact Or.inr ⟨⟨lt_of_not_ge h, hv⟩, hb⟩
    · rintro (⟨hv, hb⟩ | ⟨⟨_, hv⟩, hb⟩)
      · exact ⟨hv.trans hlr, hb⟩
      · exact ⟨hv, hb⟩
  rw [hset]
  apply measureReal_union
  · apply Set.disjoint_left.mpr
    intro v hv hw
    exact (not_lt_of_ge hv.1) hw.1.1
  · exact measurableSet_Ioc.prod measurableSet_Ici
  · finiteness
  · finiteness

theorem buyer_split (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (S : Set ℝ) (hS : MeasurableSet S) (q₀ q : ℝ) (hqq : q₀ ≤ q) :
    μ.real (S ×ˢ Set.Ici q₀) =
      μ.real (S ×ˢ Set.Ici q) + μ.real (S ×ˢ Set.Ico q₀ q) := by
  have hset : S ×ˢ Set.Ici q₀ = (S ×ˢ Set.Ici q) ∪ (S ×ˢ Set.Ico q₀ q) := by
    ext v
    simp only [Set.mem_prod, Set.mem_Ici, Set.mem_union, Set.mem_Ico]
    constructor
    · rintro ⟨hv, hb⟩
      by_cases h : q ≤ v.2
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, hb, lt_of_not_ge h⟩
    · rintro (⟨hv, hb⟩ | ⟨hv, hb, _⟩)
      · exact ⟨hv, hqq.trans hb⟩
      · exact ⟨hv, hb⟩
  rw [hset]
  apply measureReal_union
  · apply Set.disjoint_left.mpr
    intro v hv hw
    exact (not_lt_of_ge hv.2) hw.2.2
  · exact hS.prod measurableSet_Ico
  · finiteness
  · finiteness

theorem mixed_difference (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (l r q₀ q : ℝ) (hlr : l ≤ r) (hqq : q₀ ≤ q) :
    (muP μ (r, q) - muP μ (l, q)) - (muP μ (r, q₀) - muP μ (l, q₀)) =
      (r - l) * μ.real (Set.Iic l ×ˢ Set.Ico q₀ q) +
      (q - q₀) * μ.real (Set.Ioc l r ×ˢ Set.Ici q) +
      (r - q₀) * μ.real (Set.Ioc l r ×ˢ Set.Ico q₀ q) := by
  have hp := seller_split μ l r q hlr
  have hp₀ := seller_split μ l r q₀ hlr
  have hbl := buyer_split μ (Set.Iic l) measurableSet_Iic q₀ q hqq
  have hbr := buyer_split μ (Set.Ioc l r) measurableSet_Ioc q₀ q hqq
  unfold muP
  rw [hp, hp₀, trade_rectangle μ l q₀, hbl, hbr, ← trade_rectangle μ l q]
  ring

theorem restricted_volume_Ioc (l r : ℝ) (hl : 0 ≤ l) (hr : r ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Ioc l r) =
      ENNReal.ofReal (r - l) := by
  rw [Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr (by
      intro x hx
      exact ⟨hl.trans hx.1.le, hx.2.trans hr⟩), Real.volume_Ioc]

theorem restricted_volume_Ico (q₀ q : ℝ) (hq₀ : 0 ≤ q₀) (hq : q ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Ico q₀ q) =
      ENNReal.ofReal (q - q₀) := by
  rw [Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (by
      intro x hx
      exact ⟨hq₀.trans hx.1, hx.2.le.trans hq⟩), Real.volume_Ico]

theorem nu_rectangle (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (l r q₀ q : ℝ) (hl : 0 ≤ l) (hr : r ≤ 1) (hq₀ : 0 ≤ q₀) (hq : q ≤ 1)
    (hlr : l ≤ r) (hqq : q₀ ≤ q) :
    (nuMeas μ).real (Set.Ioc l r ×ˢ Set.Ico q₀ q) =
      (r - l) * (μ.map Prod.snd).real (Set.Ico q₀ q) +
      (q - q₀) * (μ.map Prod.fst).real (Set.Ioc l r) +
      μ.real (Set.Ioc l r ×ˢ Set.Ico q₀ q) := by
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    constructor
    simp [Measure.restrict_apply, Real.volume_Icc]
  unfold nuMeas
  rw [measureReal_add_apply, measureReal_add_apply,
    measureReal_prod_prod, measureReal_prod_prod]
  simp only [Measure.real, restricted_volume_Ioc l r hl hr,
    restricted_volume_Ico q₀ q hq₀ hq, ENNReal.toReal_ofReal (sub_nonneg.mpr hlr),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hqq)]
  ring

theorem buyer_marginal_bound (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (l q₀ q : ℝ) :
    μ.real (Set.Iic l ×ˢ Set.Ico q₀ q) ≤
      (μ.map Prod.snd).real (Set.Ico q₀ q) := by
  simp only [Measure.real, Measure.map_apply measurable_snd measurableSet_Ico]
  apply ENNReal.toReal_mono (by finiteness)
  exact measure_mono (fun _ hx => hx.2)

theorem seller_marginal_bound (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (l r q : ℝ) :
    μ.real (Set.Ioc l r ×ˢ Set.Ici q) ≤
      (μ.map Prod.fst).real (Set.Ioc l r) := by
  simp only [Measure.real, Measure.map_apply measurable_fst measurableSet_Ioc]
  apply ENNReal.toReal_mono (by finiteness)
  exact measure_mono (fun _ hx => hx.1)

theorem inequality (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (l r q₀ q : ℝ) (hl : l ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hq₀ : q₀ ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hlr : l ≤ r) (hqq : q₀ ≤ q) :
    |(muP μ (r, q) - muP μ (l, q)) - (muP μ (r, q₀) - muP μ (l, q₀))| ≤
      (nuMeas μ (Set.Ioc l r ×ˢ Set.Ico q₀ q)).toReal := by
  rw [mixed_difference μ l r q₀ q hlr hqq]
  change |(r - l) * μ.real (Set.Iic l ×ˢ Set.Ico q₀ q) +
      (q - q₀) * μ.real (Set.Ioc l r ×ˢ Set.Ici q) +
      (r - q₀) * μ.real (Set.Ioc l r ×ˢ Set.Ico q₀ q)| ≤
    (nuMeas μ).real (Set.Ioc l r ×ˢ Set.Ico q₀ q)
  rw [nu_rectangle μ l r q₀ q hl.1 hr.2 hq₀.1 hq.2 hlr hqq]
  have hC : 0 ≤ μ.real (Set.Iic l ×ˢ Set.Ico q₀ q) := ENNReal.toReal_nonneg
  have hB : 0 ≤ μ.real (Set.Ioc l r ×ˢ Set.Ici q) := ENNReal.toReal_nonneg
  have hD : 0 ≤ μ.real (Set.Ioc l r ×ˢ Set.Ico q₀ q) := ENNReal.toReal_nonneg
  have hcoeff : |r - q₀| ≤ 1 := abs_le.mpr ⟨by linarith [hr.1, hq₀.2], by linarith [hr.2, hq₀.1]⟩
  calc
    _ ≤ |(r - l) * μ.real (Set.Iic l ×ˢ Set.Ico q₀ q)| +
        |(q - q₀) * μ.real (Set.Ioc l r ×ˢ Set.Ici q)| +
        |(r - q₀) * μ.real (Set.Ioc l r ×ˢ Set.Ico q₀ q)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = (r - l) * μ.real (Set.Iic l ×ˢ Set.Ico q₀ q) +
        (q - q₀) * μ.real (Set.Ioc l r ×ˢ Set.Ici q) +
        |r - q₀| * μ.real (Set.Ioc l r ×ˢ Set.Ico q₀ q) := by
      rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hlr) hC),
        abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hqq) hB), abs_mul, abs_of_nonneg hD]
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left (buyer_marginal_bound μ l q₀ q) (sub_nonneg.mpr hlr)
      have hs := mul_le_mul_of_nonneg_left (seller_marginal_bound μ l r q) (sub_nonneg.mpr hqq)
      have hd := mul_le_mul_of_nonneg_right hcoeff hD
      linarith

theorem square_mass (μ : Measure (ℝ × ℝ)) (hμ : IsValLaw μ) :
    μ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = 1 := by
  have := hμ.1
  simpa using measure_of_measure_compl_eq_zero hμ.2

theorem fst_mass (μ : Measure (ℝ × ℝ)) (hμ : IsValLaw μ) :
    (μ.map Prod.fst) (Set.Icc (0 : ℝ) 1) = 1 := by
  have := hμ.1
  rw [Measure.map_apply measurable_fst measurableSet_Icc]
  have hnull : μ (Prod.fst ⁻¹' Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    apply measure_mono_null (t := (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) ?_ hμ.2
    intro v hv hw
    exact hv hw.1
  simpa using measure_of_measure_compl_eq_zero hnull

theorem snd_mass (μ : Measure (ℝ × ℝ)) (hμ : IsValLaw μ) :
    (μ.map Prod.snd) (Set.Icc (0 : ℝ) 1) = 1 := by
  have := hμ.1
  rw [Measure.map_apply measurable_snd measurableSet_Icc]
  have hnull : μ (Prod.snd ⁻¹' Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    apply measure_mono_null (t := (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) ?_ hμ.2
    intro v hv hw
    exact hv hw.2
  simpa using measure_of_measure_compl_eq_zero hnull

theorem total_mass (μ : Measure (ℝ × ℝ)) (hμ : IsValLaw μ) :
    nuMeas μ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = 3 := by
  have := hμ.1
  simp only [nuMeas, Measure.add_apply, Measure.prod_prod,
    Measure.restrict_apply measurableSet_Icc, Set.inter_self, Real.volume_Icc,
    sub_zero, ENNReal.ofReal_one, fst_mass μ hμ, snd_mass μ hμ, square_mass μ hμ,
    mul_one]
  norm_num

end BilateralProfit.Eq17

/-- Equation (17) and the total mass assertion following it, in Step 2 of the proof
of Lemma 4.8 of Brüstle, di Gregorio, Fusco, and Leonardi,
*Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best
Posted-Price Mechanism*, manuscript PDF page 26. -/
theorem solution (μ : Measure (ℝ × ℝ)) (hμ : BilateralProfit.IsValLaw μ) :
    (∀ l r q₀ q : ℝ, l ∈ Set.Icc (0 : ℝ) 1 → r ∈ Set.Icc (0 : ℝ) 1 → q₀ ∈ Set.Icc (0 : ℝ) 1 →
      q ∈ Set.Icc (0 : ℝ) 1 → l ≤ r → q₀ ≤ q →
        |(BilateralProfit.muP μ (r, q) - BilateralProfit.muP μ (l, q)) -
          (BilateralProfit.muP μ (r, q₀) - BilateralProfit.muP μ (l, q₀))| ≤
          (BilateralProfit.nuMeas μ (Set.Ioc l r ×ˢ Set.Ico q₀ q)).toReal) ∧
      BilateralProfit.nuMeas μ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = 3 := by
  have := hμ.1
  exact ⟨BilateralProfit.Eq17.inequality μ, BilateralProfit.Eq17.total_mass μ hμ⟩
