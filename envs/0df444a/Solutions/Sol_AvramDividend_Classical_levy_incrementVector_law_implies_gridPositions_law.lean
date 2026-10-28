-- Prove2me | solution 1 for AvramDividend.Classical.levy_incrementVector_law_implies_gridPositions_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:55:17.439551+00:00
-- url     : https://prove2.me/submissions/08379ced-f422-45f1-a053-862f784a5505

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_n_levy_increment_telescoping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- Equality of increment-vector laws implies equality of cumulative grid-position laws. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (n : ℕ)
    (hLaw : Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω) P =
      Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (s + t (i.val + 1)) ω - X.X (s + t 0) ω) P =
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t 0) ω) P := by
  classical
  let Y : Ω → (Fin n → ℝ) := fun ω i => X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω
  let Z : Ω → (Fin n → ℝ) := fun ω i => X.X (t (i.val + 1)) ω - X.X (t i.val) ω
  let cum : (Fin n → ℝ) → (Fin n → ℝ) := fun z i =>
    ∑ k ∈ Finset.range (i.val + 1), if hk : k < n then z ⟨k, hk⟩ else 0
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr; intro i
    exact ((X.adapted (s + t (i.val + 1))).mono (𝓕.le (s + t (i.val + 1))) le_rfl).sub
      ((X.adapted (s + t i.val)).mono (𝓕.le (s + t i.val)) le_rfl)
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr; intro i
    exact ((X.adapted (t (i.val + 1))).mono (𝓕.le (t (i.val + 1))) le_rfl).sub
      ((X.adapted (t i.val)).mono (𝓕.le (t i.val)) le_rfl)
  have hCumMeas : Measurable cum := by
    apply measurable_pi_iff.mpr; intro i
    apply Finset.measurable_sum
    intro k hk
    by_cases hkn : k < n
    · simpa only [dif_pos hkn] using (measurable_pi_apply (⟨k, hkn⟩ : Fin n))
    · simpa only [dif_neg hkn] using
        (measurable_const : Measurable (fun _ : Fin n → ℝ => (0 : ℝ)))
  have hShift (ω : Ω) (i : Fin n) :
      cum (Y ω) i = X.X (s + t (i.val + 1)) ω - X.X (s + t 0) ω := by
    have hSum : (∑ k ∈ Finset.range (i.val + 1),
        if hk : k < n then Y ω ⟨k, hk⟩ else 0) =
        ∑ k ∈ Finset.range (i.val + 1),
        (X.X (s + t (k + 1)) ω - X.X (s + t k) ω) := by
      apply Finset.sum_congr rfl; intro k hk
      have hkn : k < n := Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) i.isLt
      simp [hkn, Y]
    change (∑ k ∈ Finset.range (i.val + 1),
      if hk : k < n then Y ω ⟨k, hk⟩ else 0) = _
    rw [hSum]
    exact chat04_all_n_levy_increment_telescoping X (fun j => s + t j) (i.val + 1) ω
  have hZero (ω : Ω) (i : Fin n) :
      cum (Z ω) i = X.X (t (i.val + 1)) ω - X.X (t 0) ω := by
    have hSum : (∑ k ∈ Finset.range (i.val + 1),
        if hk : k < n then Z ω ⟨k, hk⟩ else 0) =
        ∑ k ∈ Finset.range (i.val + 1),
        (X.X (t (k + 1)) ω - X.X (t k) ω) := by
      apply Finset.sum_congr rfl; intro k hk
      have hkn : k < n := Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) i.isLt
      simp [hkn, Z]
    change (∑ k ∈ Finset.range (i.val + 1),
      if hk : k < n then Z ω ⟨k, hk⟩ else 0) = _
    rw [hSum]
    exact chat04_all_n_levy_increment_telescoping X t (i.val + 1) ω
  have hVector : Measure.map Y P = Measure.map Z P := hLaw
  calc
    _ = Measure.map (cum ∘ Y) P := by
      congr 1; funext ω i; exact (hShift ω i).symm
    _ = Measure.map cum (Measure.map Y P) := (Measure.map_map hCumMeas hY).symm
    _ = Measure.map cum (Measure.map Z P) := by rw [hVector]
    _ = Measure.map (cum ∘ Z) P := Measure.map_map hCumMeas hZ
    _ = _ := by
      congr 1; funext ω i; exact hZero ω i
