-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_atomic_cash_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:28:30.397392+00:00
-- url     : https://prove2.me/submissions/b4328076-b703-464d-9f65-7707f9d5a2a4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_true_atom_discounted_cash_summable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (θ : ℝ≥0) :
    Summable (fun s : ℝ≥0 =>
      if s ≤ θ ∧ (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) then
        Real.exp (-(q * (s : ℝ))) * (rightLimit D s ω - D s ω)
      else 0) := by 
  classical
  let μ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (θ : ℝ))
  let f : ℝ → ℝ := fun t => (μ {t} *
    (if t ∈ paymentTimes (ruinTime X x D ω) then ENNReal.ofReal (Real.exp (-(q * t))) else 0)).toReal
  obtain ⟨A, hA, hSupp, hSum⟩ := avram_p4_d_dividend_original_stopped_true_atom_discounted_cash_summable X x q hq D hD ω θ
  have hi : Summable (A.indicator f) := summable_subtype_iff_indicator.mp hSum
  have hf : Summable f := by
    refine hi.congr (fun t => ?_)
    by_cases ht : t ∈ A
    · exact indicator_of_mem ht _
    · have hm : μ {t} = 0 := by by_contra hn; exact ht (hSupp t hn)
      simp [f, ht, hm]
  have hs : Summable (fun s : ℝ≥0 => f (s : ℝ)) := hf.comp_injective Subtype.coe_injective
  refine hs.congr (fun s => ?_)
  have hd := dividendStrategy_le_rightLimit D hD ω s
  have hmem : (s : ℝ) ∈ paymentTimes (ruinTime X x D ω) ↔
      s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω := by
    simp [paymentTimes, ENNReal.ofReal_coe_nnreal]
  by_cases hle : s ≤ θ
  · have hm : μ {(s : ℝ)} = ENNReal.ofReal (rightLimit D s ω - D s ω) := by
      rw [Measure.restrict_apply (measurableSet_singleton _)]
      rw [Set.singleton_inter_of_mem (show (s : ℝ) ∈ Icc (0 : ℝ) (θ : ℝ) from ⟨s.2, by exact_mod_cast hle⟩)]
      exact dividendMeasure_singleton_eq_rightLimit_sub D hD ω s
    by_cases hp : s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω
    · simp [f, hm, hle, hp, hmem, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hd), ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_comm]
    · simp [f, hle, hp, hmem]
  · have hm : μ {(s : ℝ)} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton _)]
      have hn : (s : ℝ) ∉ Icc (0 : ℝ) (θ : ℝ) := fun h => hle (by exact_mod_cast h.2)
      simp [Set.singleton_inter_of_notMem hn]
    simp [f, hm, hle]
