-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_ruincontact_full_final_Ioc_cash_strict_tail_plus_exact_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:56:10.622004+00:00
-- url     : https://prove2.me/submissions/d42acc09-4f4f-42e9-a0b4-cb2ff8d2edca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (q : ℝ) (n : ℕ) (hn : 0 < n) (j : ℕ) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ {(T : ℝ)},
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
  let S : Set ℝ := paymentTimes (ruinTime X x D ω)
  let a : ℝ := (T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-(q * s)))
  let μ : Measure ℝ := dividendMeasure D ω
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hgap : a < (T : ℝ) := by
    dsimp [a]
    have hwidth : 0 < (n : ℝ) / ((j : ℝ) + 1) :=
      div_pos hnReal (by positivity)
    linarith
  have hMeasB : MeasurableSet (S ∩ {(T : ℝ)}) :=
    (avram_p4_d_dividend_original_paymentTimes_measurableSet
      (ruinTime X x D ω)).inter (measurableSet_singleton (T : ℝ))
  have hDis : Disjoint (S ∩ Ioo a (T : ℝ)) (S ∩ {(T : ℝ)}) := by
    apply Set.disjoint_left.mpr
    intro s hs hlast
    have hlt : s < (T : ℝ) := hs.2.2
    have heq : s = (T : ℝ) := hlast.2
    exact (lt_irrefl (T : ℝ)) (heq ▸ hlt)
  have hSet :
      S ∩ Ioc a (T : ℝ) =
        (S ∩ Ioo a (T : ℝ)) ∪ (S ∩ {(T : ℝ)}) := by
    ext s
    simp only [mem_inter_iff, mem_union, mem_Ioc, mem_Ioo, mem_singleton_iff]
    constructor
    · rintro ⟨hs, hlo, hhi⟩
      by_cases heq : s = (T : ℝ)
      · exact Or.inr ⟨hs, heq⟩
      · exact Or.inl ⟨hs, hlo, lt_of_le_of_ne hhi heq⟩
    · rintro (⟨hs, hlo, hhi⟩ | ⟨hs, heq⟩)
      · exact ⟨hs, hlo, hhi.le⟩
      · subst s
        exact ⟨hs, hgap, le_rfl⟩
  change (∫⁻ s in S ∩ Ioc a (T : ℝ), f s ∂μ) =
      (∫⁻ s in S ∩ Ioo a (T : ℝ), f s ∂μ) +
      (∫⁻ s in S ∩ {(T : ℝ)}, f s ∂μ)
  rw [hSet]
  exact lintegral_union hMeasB hDis
