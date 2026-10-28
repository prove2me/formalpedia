-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_terminal_extended_clock_discount_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:04:38.161002+00:00
-- url     : https://prove2.me/submissions/27d05ab2-6c3a-45da-bdb1-1faec61cf718

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_partial_record_cell_upper

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞))) :
    (∫⁻ r,
      if r ∈ Set.Ioc (u : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h := by
  have hw : Antitone (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r)))) := by
    intro r r' hrr
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
  have hXu := (AvramDividend.Classical.firstUpcrossing_attains_peak X b hb ω u hu).1
  have hs : AvramDividend.Classical.runningSup X (u : ℝ).toNNReal ω = b := by
    rw [Real.toNNReal_coe]
    have := AvramDividend.Classical.firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u hu
    linarith
  have ht' : AvramDividend.Classical.runningSup X (t : ℝ).toNNReal ω ≤ b + h := by
    rw [Real.toNNReal_coe, (AvramDividend.Classical.runningSup_eq_rawSup_nonneg X t ω).1]
    rcases lt_or_eq_of_le ht with hlt | heq
    · haveI : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, zero_le⟩⟩
      refine ciSup_le fun s => ?_
      by_contra hc
      push_neg at hc
      have h1 : (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞)) ≤ s.1 := iInf₂_le s.1 hc
      have h2 : (s.1 : ℝ≥0∞) ≤ t := ENNReal.coe_le_coe.2 s.2.2
      exact absurd (lt_of_le_of_lt (h1.trans h2) hlt) (lt_irrefl _)
    · obtain ⟨hXt, hsup⟩ := AvramDividend.Classical.firstUpcrossing_attains_peak X (b + h) (by linarith) ω t heq
      have e : (⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω) = sSup ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 t) :=
        (sSup_image' (s := Set.Icc (0 : ℝ≥0) t) (f := fun r : ℝ≥0 => X.X r ω)).symm
      rw [e, hsup, hXt]
  exact AvramDividend.Classical.runningSup_discounted_partial_record_cell_upper X ω _ hw u t b h hh hs ht' 
