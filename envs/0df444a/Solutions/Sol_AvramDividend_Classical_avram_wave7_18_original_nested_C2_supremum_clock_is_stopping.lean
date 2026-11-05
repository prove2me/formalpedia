-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_nested_C2_supremum_clock_is_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:32:13.538673+00:00
-- url     : https://prove2.me/submissions/0b118c77-b54b-43ab-a75c-39899eb33bb7

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (lower upper : ℕ → ℝ) (B : ℕ → ℝ≥0)
    (hlower : ∀ n, 0 < lower n)
    (hlo : ∀ n, lower (n + 1) ≤ lower n)
    (hup : ∀ n, upper n ≤ upper (n + 1))
    (hcap : ∀ n, ∀ y ∈ Set.Icc (lower n) (upper n), ENNReal.ofReal y < C)
    (hB : ∀ n, B n ≤ B (n + 1)) :
    let τ : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)
    IsStoppingTime 𝓕.rightCont (fun ω : Ω => ⨆ n, τ n ω) := by
  dsimp only
  have hstage : ∀ n, IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)) := by
    intro n
    exact (avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
      X x D hD C w hw r (lower n) (upper n)
      (hlower n) (hcap n) hdense (B n)).1
  intro t
  change MeasurableSet[𝓕.rightCont t]
    {ω : Ω | (⨆ n : ℕ, min (⨅ k : ℕ,
      if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
          upper n < x + X.X (r k) ω - rightLimit D (r k) ω
      then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)) ≤
        (t : WithTop ℝ≥0)}
  have hEq :
      {ω : Ω | (⨆ n : ℕ, min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)) ≤
          (t : WithTop ℝ≥0)} =
      ⋂ n : ℕ, {ω : Ω | min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0) ≤
          (t : WithTop ℝ≥0)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, iSup_le_iff]
  rw [hEq]
  exact MeasurableSet.iInter (fun n => hstage n t)
