-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_gaussian_small_large_rightatom_modulus_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:38:51.353354+00:00
-- url     : https://prove2.me/submissions/5ecfff4c-c582-4d79-b90b-92c07bba6192

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open BigOperators AvramDividend.Classical
noncomputable section
set_option autoImplicit false

/-- Finite original dividend atom small/large Hessian-modulus energy
bound follows from total atom mass and cellwise modulus control. -/
theorem solution
    (m : ℕ) (Δ ε K δ B : ℝ) (atom modulus : ℕ → ℝ)
    (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hAtom : ∑ i ∈ Finset.range m, atom i ≤ B)
    (hMod : ∀ i ∈ Finset.range m,
      modulus i ≤ ε + (K / δ) * atom i) :
    Δ * (∑ i ∈ Finset.range m, modulus i) ≤
      Δ * ((m : ℝ) * ε + (K / δ) * B) := by
  have hpoint : (∑ i ∈ Finset.range m, modulus i) ≤
      ∑ i ∈ Finset.range m, (ε + (K / δ) * atom i) := by
    exact Finset.sum_le_sum hMod
  have hsum : (∑ i ∈ Finset.range m, modulus i) ≤
      (m : ℝ) * ε + (K / δ) * B := by
    calc
      _ ≤ ∑ i ∈ Finset.range m, (ε + (K / δ) * atom i) := hpoint
      _ = (m : ℝ) * ε + (K / δ) *
          (∑ i ∈ Finset.range m, atom i) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum, mul_comm, Finset.sum_mul]
      _ ≤ (m : ℝ) * ε + (K / δ) * B := by
            exact add_le_add_right
              (mul_le_mul_of_nonneg_left hAtom (div_nonneg hK (le_of_lt hδ)))
              ((m : ℝ) * ε)
  exact mul_le_mul_of_nonneg_left hsum hΔ
