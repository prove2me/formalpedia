-- Prove2me | solution 1 for AvramDividend.Classical.levy_equal_mesh_path_drawdown_minimum_threshold_ws01e_b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:50:30.979243+00:00
-- url     : https://prove2.me/submissions/c6e6e0f7-3b8b-4142-855e-eab6b024a609

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_drawdown_minimum_event_law_ws01e_b
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
/-- Direct original-path finite-grid Lévy drawdown/minimum probability symmetry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ) (a : ℝ) :
    P {ω : Ω | ∃ k : Fin n.succ,
      X.X ((n : ℝ≥0) * δ) ω -
        X.X ((k.val : ℝ≥0) * δ) ω ≤ a} =
    P {ω : Ω | ∃ k : Fin n.succ,
      X.X ((k.val : ℝ≥0) * δ) ω - X.X 0 ω ≤ a} := by
  let inc : Ω → ℕ → ℝ := fun ω j =>
    if j < n then X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((j : ℝ≥0) * δ) ω else 0
  let prefSum : (ℕ → ℝ) → ℕ → ℝ := fun v k => Finset.sum (Finset.range k) v
  let L : Set (ℕ → ℝ) := {v | ∃ k : Fin n.succ, prefSum v n - prefSum v k.val ≤ a}
  let R : Set (ℕ → ℝ) := {v | ∃ k : Fin n.succ, prefSum v k.val ≤ a}
  have hinc : Measurable inc := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j < n
    · have ht : Measurable (X.X (((j + 1 : ℕ) : ℝ≥0) * δ)) := X.adapted.measurable
      have hs : Measurable (X.X ((j : ℝ≥0) * δ)) := X.adapted.measurable
      convert ht.sub hs using 1
      funext ω
      simp [inc, hj, Pi.sub_apply]
    · simpa only [inc, if_neg hj] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  have hsum (ω : Ω) (k : ℕ) (hk : k ≤ n) : prefSum (inc ω) k = X.X ((k : ℝ≥0) * δ) ω - X.X 0 ω := by
    induction k with
    | zero => simp [prefSum]
    | succ k ih =>
      have hkn : k < n := Nat.lt_of_succ_le hk
      rw [show prefSum (inc ω) (k + 1) = prefSum (inc ω) k + inc ω k by
        simp [prefSum, Finset.sum_range_succ]]
      rw [ih (Nat.le_of_lt hkn)]
      simp only [inc, if_pos hkn]
      ring
  have hPref (k : ℕ) : Measurable (fun v : ℕ → ℝ => prefSum v k) := Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)
  have hL : MeasurableSet L := by
    have hu : MeasurableSet (⋃ k : Fin n.succ, {v : ℕ → ℝ | prefSum v n - prefSum v k.val ≤ a}) :=
      MeasurableSet.iUnion (fun k => measurableSet_le ((hPref n).sub (hPref k.val)) measurable_const)
    simpa only [L, Set.setOf_exists] using hu
  have hR : MeasurableSet R := by
    have hu : MeasurableSet (⋃ k : Fin n.succ, {v : ℕ → ℝ | prefSum v k.val ≤ a}) :=
      MeasurableSet.iUnion (fun k => measurableSet_le (hPref k.val) measurable_const)
    simpa only [R, Set.setOf_exists] using hu
  have hEventL (ω : Ω) : (∃ k : Fin n.succ,
      X.X ((n : ℝ≥0) * δ) ω - X.X ((k.val : ℝ≥0) * δ) ω ≤ a) ↔ inc ω ∈ L := by
    change (∃ k : Fin n.succ, X.X ((n : ℝ≥0) * δ) ω - X.X ((k.val : ℝ≥0) * δ) ω ≤ a) ↔
      (∃ k : Fin n.succ, prefSum (inc ω) n - prefSum (inc ω) k.val ≤ a)
    apply exists_congr
    intro k
    rw [hsum ω n le_rfl, hsum ω k.val (Nat.le_of_lt_succ k.isLt)]
    constructor <;> intro h <;> linarith
  have hEventR (ω : Ω) : (∃ k : Fin n.succ,
      X.X ((k.val : ℝ≥0) * δ) ω - X.X 0 ω ≤ a) ↔ inc ω ∈ R := by
    change (∃ k : Fin n.succ, X.X ((k.val : ℝ≥0) * δ) ω - X.X 0 ω ≤ a) ↔
      (∃ k : Fin n.succ, prefSum (inc ω) k.val ≤ a)
    apply exists_congr
    intro k
    rw [hsum ω k.val (Nat.le_of_lt_succ k.isLt)]
  have hLaw : (Measure.map inc P) L = (Measure.map inc P) R := levy_equal_mesh_drawdown_minimum_event_law_ws01e_b X δ n a
  calc
    P {ω : Ω | ∃ k : Fin n.succ,
        X.X ((n : ℝ≥0) * δ) ω -
          X.X ((k.val : ℝ≥0) * δ) ω ≤ a} =
      (Measure.map inc P) L := by
        rw [Measure.map_apply hinc hL]; congr 1; ext ω; exact hEventL ω
    _ = (Measure.map inc P) R := hLaw
    _ = P {ω : Ω | ∃ k : Fin n.succ,
        X.X ((k.val : ℝ≥0) * δ) ω - X.X 0 ω ≤ a} := by
        rw [Measure.map_apply hinc hR]; congr 1; ext ω; exact (hEventR ω).symm
