-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:30:48.881199+00:00
-- url     : https://prove2.me/submissions/4f306567-cbe0-4d00-9443-609632c141b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n)) :
    (∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => ⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω))) ∧
    (∀ n : ℕ, Measurable
      (fun ω => ⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω))) ∧
    (∀ ω, Monotone
      (fun n : ℕ => ⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω))) := by
  have hruin : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    ruinTime_stopping_rightCont_filtration X x D hD.1.1
  have hstop : ∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => ⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) := by
    intro n
    exact IsStoppingTime.iInf
      (fun k : ℕ => hruin.min (hSstop (n + k)))
  refine ⟨hstop, ?_, ?_⟩
  · intro n
    exact (hstop n).measurable'
  · intro ω n m hnm
    refine le_iInf (fun k => ?_)
    have hindex : n + ((m - n) + k) = m + k := by omega
    have hle :
        (⨅ j : ℕ, min (ruinTime X x D ω) (S (n + j) ω)) ≤
        min (ruinTime X x D ω) (S (n + ((m - n) + k)) ω) :=
      iInf_le (fun j : ℕ =>
        min (ruinTime X x D ω) (S (n + j) ω)) ((m - n) + k)
    simpa only [hindex] using hle
end
