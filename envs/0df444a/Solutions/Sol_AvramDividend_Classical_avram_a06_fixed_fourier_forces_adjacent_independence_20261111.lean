-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_fixed_fourier_forces_adjacent_independence_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:32:19.817696+00:00
-- url     : https://prove2.me/submissions/ff5c6e36-463d-4eea-a15b-94659a0e4352

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_fourier_factor_implies_block_independence_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

/-- Fixed-grid Fourier factorisation forces adjacent-block independence. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n) (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j))
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
            (t.ofLp i))
    (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    IndepFun (fun ω => ∑ j ∈ Finset.Ico a b, Y j ω)
      (fun ω => ∑ j ∈ Finset.Ico b c, Y j ω) P := by
  let m : Fin (n + 1) → ℕ := fun i =>
    if i.val = 0 then a else if i.val = 1 then b else c
  have hm : Monotone m := by
    intro i j hij
    dsimp [m]
    have hv : i.val ≤ j.val := hij
    split_ifs <;> omega
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by
    simp [i0, i1]
  have hInd : iIndepFun (fun i : Fin n => fun ω : Ω =>
      ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P :=
    AvramDividend.Classical.avram_a06_fixed_fourier_factor_implies_block_independence_20261111
      P n Y hY hFixed m hm
  have hpair := hInd.indepFun hne
  simpa [m, i0, i1] using hpair
