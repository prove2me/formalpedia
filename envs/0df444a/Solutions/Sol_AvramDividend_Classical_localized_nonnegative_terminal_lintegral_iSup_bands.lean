-- Prove2me | solution 1 for AvramDividend.Classical.localized_nonnegative_terminal_lintegral_iSup_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:24:51.598988+00:00
-- url     : https://prove2.me/submissions/9d9009da-0bd9-4e34-8eca-f88533c9ca1e

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Classical ENNReal

/-- Finite reserve-band terminal expectations exhaust the unrestricted nonnegative-reserve payoff. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (r : Ω → ℝ) (hr : Measurable r)
    (w : ℝ → ℝ) (hw : Measurable w) :
    (∫⁻ ω, if ω ∈ A ∧ 0 ≤ r ω then ENNReal.ofReal (w (r ω)) else 0 ∂P) =
      ⨆ n : ℕ, (∫⁻ ω,
        if ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (n : ℝ) then
          ENNReal.ofReal (w (r ω)) else 0 ∂P) := by
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (n : ℝ) then
      ENNReal.ofReal (w (r ω)) else 0
  have hMeasW : Measurable (fun ω => ENNReal.ofReal (w (r ω))) :=
    ENNReal.measurable_ofReal.comp (hw.comp hr)
  have hf : ∀ n, Measurable (f n) := by
    intro n
    have h0 : MeasurableSet {ω : Ω | 0 ≤ r ω} :=
      measurableSet_Ici.preimage hr
    have hn : MeasurableSet {ω : Ω | r ω ≤ (n : ℝ)} :=
      measurableSet_Iic.preimage hr
    have hset : MeasurableSet {ω : Ω |
        ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (n : ℝ)} := by
      simpa [Set.setOf_and] using (hA.inter h0).inter (hA.inter hn)
    exact Measurable.ite hset hMeasW measurable_const
  have hmono : Monotone f := by
    intro n m hnm ω
    by_cases h : ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (n : ℝ)
    · have hm : ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (m : ℝ) :=
        ⟨h.1, h.2.1, le_trans h.2.2 (by exact_mod_cast hnm)⟩
      simp [f, h, hm]
    · simp [f, h]
  have hpoint : ∀ ω, (⨆ n, f n ω) =
      if ω ∈ A ∧ 0 ≤ r ω then ENNReal.ofReal (w (r ω)) else 0 := by
    intro ω
    by_cases h : ω ∈ A ∧ 0 ≤ r ω
    · obtain ⟨n, hn⟩ := exists_nat_ge (r ω)
      have hn' : ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (n : ℝ) :=
        ⟨h.1, h.2, hn⟩
      apply le_antisymm
      · refine iSup_le fun k => ?_
        by_cases hk : ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (k : ℝ)
        · simp [f, h, hk]
        · have hnot : ¬ r ω ≤ (k : ℝ) := by
            intro hle
            exact hk ⟨h.1, h.2, hle⟩
          simp [f, h, hnot]
      · calc
          (if ω ∈ A ∧ 0 ≤ r ω then ENNReal.ofReal (w (r ω)) else 0) =
              f n ω := by simp [f, h, hn']
          _ ≤ ⨆ k, f k ω := le_iSup (fun k => f k ω) n
    · have hzero : ∀ n, f n ω = 0 := by
        intro n
        have hn : ¬(ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (n : ℝ)) := by
          intro hh
          exact h ⟨hh.1, hh.2.1⟩
        simp [f, hn]
      simp [h, hzero]
  calc
    (∫⁻ ω, if ω ∈ A ∧ 0 ≤ r ω then ENNReal.ofReal (w (r ω)) else 0 ∂P) =
        ∫⁻ ω, ⨆ n, f n ω ∂P := by congr 1; funext ω; exact (hpoint ω).symm
    _ = ⨆ n, ∫⁻ ω, f n ω ∂P := lintegral_iSup hf hmono
    _ = ⨆ n : ℕ, (∫⁻ ω,
        if ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (n : ℝ) then
          ENNReal.ofReal (w (r ω)) else 0 ∂P) := rfl
