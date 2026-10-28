-- Prove2me | solution 1 for AvramDividend.Classical.levy_equal_mesh_drawdown_minimum_event_law_ws01e_b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:16:50.237454+00:00
-- url     : https://prove2.me/submissions/65096fe7-fc24-4a41-b7b4-2bdcef56138b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_drawdown_minimum_event_probability_of_reversal_ws01e_b
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_increment_vector_law_reversal_ws01e_b

set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine Lévy finite-grid drawdown and minimum share threshold probabilities. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ) (a : ℝ) :
    let inc : Ω → ℕ → ℝ := fun ω j =>
      if j < n then
        X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((j : ℝ≥0) * δ) ω
      else 0
    let ν : Measure (ℕ → ℝ) := Measure.map inc P
    ν {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) v -
        Finset.sum (Finset.range k.val) v ≤ a} =
    ν {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) v ≤ a} := by
  let inc : Ω → ℕ → ℝ := fun ω j =>
    if j < n then
      X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((j : ℝ≥0) * δ) ω
    else 0
  let vec : Ω → Fin n → ℝ := fun ω i =>
    X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω
  let pad : (Fin n → ℝ) → ℕ → ℝ :=
    fun v j => if hj : j < n then v ⟨j, hj⟩ else 0
  let revFin : (Fin n → ℝ) → Fin n → ℝ :=
    fun v i => v i.rev
  let revNat : (ℕ → ℝ) → ℕ → ℝ :=
    fun v j => if j < n then v (n - 1 - j) else v j
  change (Measure.map inc P)
      {v : ℕ → ℝ | ∃ k : Fin n.succ,
        Finset.sum (Finset.range n) v -
          Finset.sum (Finset.range k.val) v ≤ a} =
    (Measure.map inc P)
      {v : ℕ → ℝ | ∃ k : Fin n.succ,
        Finset.sum (Finset.range k.val) v ≤ a}
  have hVecMeas : Measurable vec :=
    measurable_pi_lambda _ (fun i =>
      (X.adapted.measurable).sub (X.adapted.measurable))
  have hPadMeas : Measurable pad := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j < n
    · simpa only [pad, dif_pos hj] using
        (measurable_pi_apply (⟨j, hj⟩ : Fin n))
    · simpa only [pad, dif_neg hj] using
        (measurable_const : Measurable (fun _ : Fin n → ℝ => (0 : ℝ)))
  have hRevFinMeas : Measurable revFin :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.rev)
  have hRevNatMeas : Measurable revNat := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j < n
    · simpa only [revNat, if_pos hj] using
        (measurable_pi_apply (n - 1 - j) :
          Measurable (fun v : ℕ → ℝ => v (n - 1 - j)))
    · simpa only [revNat, if_neg hj] using
        (measurable_pi_apply j :
          Measurable (fun v : ℕ → ℝ => v j))
  have hPadRev (v : Fin n → ℝ) :
      revNat (pad v) = pad (revFin v) := by
    funext j
    by_cases hj : j < n
    · have hback : n - 1 - j < n := by omega
      simp only [revNat, if_pos hj]
      dsimp [pad, revFin]
      rw [dif_pos hback, dif_pos hj]
      congr 1
      apply Fin.ext
      simp [Fin.rev]
      omega
    · simp [revNat, pad, hj]
  have hVecLaw :
      Measure.map revFin (Measure.map vec P) =
      Measure.map vec P := by
    calc
      Measure.map revFin (Measure.map vec P) =
        Measure.map (revFin ∘ vec) P :=
        Measure.map_map hRevFinMeas hVecMeas
      _ = Measure.map vec P := by
        change Measure.map (fun ω : Ω => fun i : Fin n =>
          X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
            X.X ((i.rev.val : ℝ≥0) * δ) ω) P =
          Measure.map (fun ω : Ω => fun i : Fin n =>
            X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
              X.X ((i.val : ℝ≥0) * δ) ω) P
        exact (levy_equal_mesh_increment_vector_law_reversal_ws01e_b X δ n).symm
  have hNatLaw :
      Measure.map revNat (Measure.map pad (Measure.map vec P)) =
        Measure.map pad (Measure.map vec P) := by
    calc
      Measure.map revNat (Measure.map pad (Measure.map vec P)) =
        Measure.map (revNat ∘ pad) (Measure.map vec P) :=
        Measure.map_map hRevNatMeas hPadMeas
      _ = Measure.map (pad ∘ revFin) (Measure.map vec P) := by
        congr 1
        funext v
        exact hPadRev v
      _ = Measure.map pad (Measure.map revFin (Measure.map vec P)) :=
        (Measure.map_map hPadMeas hRevFinMeas).symm
      _ = Measure.map pad (Measure.map vec P) := by
        rw [hVecLaw]
  have hIncEq (ω : Ω) : inc ω = pad (vec ω) := by
    funext j
    by_cases hj : j < n
    · simp [inc, pad, vec, hj]
    · simp [inc, pad, hj]
  have hIncLaw : Measure.map inc P =
      Measure.map pad (Measure.map vec P) := by
    calc
      Measure.map inc P = Measure.map (pad ∘ vec) P := by
        have hfun : inc = pad ∘ vec := by
          funext ω
          exact hIncEq ω
        rw [hfun]
      _ = Measure.map pad (Measure.map vec P) :=
        (Measure.map_map hPadMeas hVecMeas).symm
  rw [hIncLaw]
  exact finite_grid_drawdown_minimum_event_probability_of_reversal_ws01e_b
    n (Measure.map pad (Measure.map vec P)) a hNatLaw
