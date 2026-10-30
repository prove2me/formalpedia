-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_dividend_strategy_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:37:17.130518+00:00
-- url     : https://prove2.me/submissions/6dd24136-bb36-4d03-8d26-0821cd00b85a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal NNRat ENNReal

/-- A monotone left-continuous path attains every strict upper level
at an earlier nonnegative rational time. -/
private theorem avram_wave3_04_density_private
    (f : ℝ≥0 → ℝ)
    (hm : Monotone f)
    (hc : ∀ t, ContinuousWithinAt f (Set.Iic t) t)
    (t : ℝ≥0) (a : ℝ)
    (ht : t ≠ 0) (ha : a < f t) :
    ∃ r : ℚ≥0, (r : ℝ≥0) < t ∧ a < f (r : ℝ≥0) := by
  have hpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht
  letI : (nhdsWithin t (Set.Iio t)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
  have hc' : ContinuousWithinAt f (Set.Iio t) t :=
    (hc t).mono (by
      intro s hs
      exact le_of_lt (Set.mem_Iio.mp hs))
  have hev : ∀ᶠ s in nhdsWithin t (Set.Iio t), a < f s :=
    hc'.eventually (isOpen_Ioi.mem_nhds ha)
  have hev_lt : ∀ᶠ s in nhdsWithin t (Set.Iio t), s < t :=
    self_mem_nhdsWithin
  obtain ⟨s, hslt, hsval⟩ := (hev_lt.and hev).exists
  rcases (NNReal.lt_iff_exists_rat_btwn s t).mp hslt with
    ⟨q, hq0, hqs, hqt⟩
  let r : ℚ≥0 := ⟨q, hq0⟩
  have hqreal : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have heq : (r : ℝ≥0) = (q : ℝ).toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ hqreal]
    change ((⟨q, hq0⟩ : ℚ≥0) : ℝ) = (q : ℝ)
    exact NNRat.cast_mk q hq0
  refine ⟨r, ?_, ?_⟩
  · simpa [heq] using hqt
  · exact lt_of_lt_of_le hsval (hm (le_of_lt (by simpa [heq] using hqs)))

/-- A monotone adapted process with zero initial value and countable
strict-left approximation has measurable predictable evaluation. -/
private theorem avram_wave3_04_predictable_rational_private
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ)
    (hzero : ∀ ω, D 0 ω = 0)
    (hadapt : Adapted 𝓕 D)
    (hmono : ∀ ω, Monotone (fun t => D t ω))
    (hdense : ∀ ω t (a : ℝ), t ≠ 0 → a < D t ω →
      ∃ r : ℚ≥0, (r : ℝ≥0) < t ∧ a < D (r : ℝ≥0) ω) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable inferInstance
      (fun p => D p.1 p.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  apply measurable_of_Ioi
  intro a
  by_cases ha : a < 0
  · have hfull : (fun p : ℝ≥0 × Ω => D p.1 p.2) ⁻¹' Set.Ioi a =
        Set.univ := by
      ext p
      have hpnonneg : 0 ≤ D p.1 p.2 := by
        have h := hmono p.2 (bot_le : (0 : ℝ≥0) ≤ p.1)
        simpa [hzero p.2] using h
      simp [Set.mem_preimage, Set.mem_Ioi, lt_of_lt_of_le ha hpnonneg]
    rw [hfull]
    exact MeasurableSet.univ
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    have hparts : ∀ r : ℚ≥0,
        MeasurableSet (Set.Ioi (r : ℝ≥0) ×ˢ
          {ω : Ω | a < D (r : ℝ≥0) ω}) := by
      intro r
      have hm : @Measurable Ω ℝ (𝓕 (r : ℝ≥0)) inferInstance
          (D (r : ℝ≥0)) := hadapt _
      exact measurableSet_predictable_Ioi_prod (hm isOpen_Ioi.measurableSet)
    have heq : (fun p : ℝ≥0 × Ω => D p.1 p.2) ⁻¹' Set.Ioi a =
        ⋃ r : ℚ≥0, Set.Ioi (r : ℝ≥0) ×ˢ
          {ω : Ω | a < D (r : ℝ≥0) ω} := by
      ext p
      constructor
      · intro hp
        have hpval : a < D p.1 p.2 := hp
        have ht : p.1 ≠ 0 := by
          intro he
          have hbad : a < 0 := by simpa [he, hzero p.2] using hpval
          exact (not_lt_of_ge ha0) hbad
        obtain ⟨r, hrlt, hrval⟩ := hdense p.2 p.1 a ht hpval
        exact Set.mem_iUnion.mpr ⟨r, ⟨hrlt, hrval⟩⟩
      · intro hp
        rcases Set.mem_iUnion.mp hp with ⟨r, hrlt, hrval⟩
        exact lt_of_lt_of_le hrval (hmono p.2 (le_of_lt hrlt))
    rw [heq]
    exact MeasurableSet.iUnion hparts

/-- The source's adapted nondecreasing left-continuous dividend control
is predictable in the original filtration, without usual augmentation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable inferInstance
      (fun p => D p.1 p.2) := by
  rcases hD with ⟨hzero, hmono, hleft, hadapt⟩
  apply avram_wave3_04_predictable_rational_private 𝓕 D hzero hadapt hmono
  intro ω t a ht ha
  exact avram_wave3_04_density_private (fun s => D s ω)
    (hmono ω) (hleft ω) t a ht ha
