-- Prove2me | solution 1 for AvramDividend.Classical.renewal_measure_atom_plus_real_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:04:30.932361+00:00
-- url     : https://prove2.me/submissions/11448e66-d3aa-41b4-92ec-8258a8dcbc5b

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_countable_real_density_measure_sum_eq_real_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped ENNReal NNReal

/-- Extract the renewal atom at zero and identify the remaining positive real series density. -/
theorem solution
    (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hFsummable : ∀ x : ℝ,
      Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else F (n - 1) x))
    (hmzero : m 0 = Measure.dirac (0 : ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x))) :
    Measure.sum m = Measure.dirac (0 : ℝ) +
      volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal (∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) x)) := by
  classical
  let G : ℕ → ℝ → ℝ := fun n x => if n = 0 then 0 else F (n - 1) x
  let mt : ℕ → Measure ℝ := fun n => if n = 0 then 0 else m n
  have hGmeas (n : ℕ) : Measurable (G n) := by
    cases n with
    | zero => simp [G]
    | succ n => simpa [G] using hFmeas n
  have hGpos (n : ℕ) (x : ℝ) : 0 ≤ G n x := by
    cases n with
    | zero => simp [G]
    | succ n => simpa [G] using hFpos n x
  have hmt (n : ℕ) :
      mt n = volume.withDensity (fun x : ℝ => ENNReal.ofReal (G n x)) := by
    cases n with
    | zero => simp [mt, G]
    | succ n => simpa [mt, G] using hmsucc n
  have hdens := countable_real_density_measure_sum_eq_real_tsum
    G mt hGmeas hGpos (by simpa [G] using hFsummable) hmt
  have hsplit : Measure.sum m = m 0 + Measure.sum mt := by
    apply Measure.ext
    intro s hs
    rw [Measure.sum_apply _ hs, Measure.add_apply _ _ s, Measure.sum_apply _ hs]
    have heval (n : ℕ) :
        mt n s = if n = 0 then 0 else m n s := by
      by_cases hn : n = 0 <;> simp [mt, hn]
    simp_rw [heval]
    convert (ENNReal.tsum_eq_add_tsum_ite (f := fun n : ℕ => m n s) 0) using 1
    congr 1
    apply congrArg (fun h : ℕ → ℝ≥0∞ => ∑' n : ℕ, h n)
    funext n
    by_cases hn : n = 0 <;> simp [hn]
  rw [hsplit, hmzero, hdens]
