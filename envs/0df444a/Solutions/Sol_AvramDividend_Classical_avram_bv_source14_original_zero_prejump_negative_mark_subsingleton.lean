-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_source14_original_zero_prejump_negative_mark_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:31:22.518198+00:00
-- url     : https://prove2.me/submissions/2f7a9a4b-378b-4332-b7ef-a4d3cf474c6c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An original negative jump from exactly zero prepayment reserve forces ruin
at that clock. The ruin clock therefore supports at most one such marked time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Set.Subsingleton {t : ℝ≥0 |
      (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω = 0 ∧
      X.X t ω < Function.leftLim (fun s : ℝ≥0 => X.X s ω) t} := by
  intro t ht u hu
  rcases ht with ⟨htBefore, htZero, htJump⟩
  rcases hu with ⟨huBefore, huZero, huJump⟩
  have htNeg : riskProcess X x D t ω < 0 := by
    dsimp [riskProcess]
    linarith
  have huNeg : riskProcess X x D u ω < 0 := by
    dsimp [riskProcess]
    linarith
  have htRuin : ruinTime X x D ω ≤ (t : ℝ≥0∞) := by
    unfold ruinTime
    exact le_trans
      (iInf_le (fun v : ℝ≥0 =>
        ⨅ (_ : riskProcess X x D v ω < 0), (v : ℝ≥0∞)) t)
      (iInf_le (fun _ : riskProcess X x D t ω < 0 => (t : ℝ≥0∞)) htNeg)
  have huRuin : ruinTime X x D ω ≤ (u : ℝ≥0∞) := by
    unfold ruinTime
    exact le_trans
      (iInf_le (fun v : ℝ≥0 =>
        ⨅ (_ : riskProcess X x D v ω < 0), (v : ℝ≥0∞)) u)
      (iInf_le (fun _ : riskProcess X x D u ω < 0 => (u : ℝ≥0∞)) huNeg)
  have htEq : (t : ℝ≥0∞) = ruinTime X x D ω :=
    le_antisymm htBefore htRuin
  have huEq : (u : ℝ≥0∞) = ruinTime X x D ω :=
    le_antisymm huBefore huRuin
  exact_mod_cast htEq.trans huEq.symm
