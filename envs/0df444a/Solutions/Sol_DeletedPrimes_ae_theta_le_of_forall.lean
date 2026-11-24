-- Prove2me | solution 1 for DeletedPrimes.ae_theta_le_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:18:35.183803+00:00
-- url     : https://prove2.me/submissions/a5543952-0e40-49e0-ad82-148814172cf5

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
import Theorems.Thm_DeletedPrimes_theta_le_of_isRegular


set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → Set ℕ) {β₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (h : ∀ β : ℝ, β₀ < β → ∀ᵐ ω ∂P, IsRegular (S ω) β) :
    ∀ᵐ ω ∂P, theta (S ω) ≤ β₀ := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, IsRegular (S ω) (β₀ + 1 / ((n : ℝ) + 1)) :=
    ae_all_iff.mpr fun n => h _ (by linarith [hpos n])
  filter_upwards [hall] with ω hω
  have hle : ∀ n : ℕ, theta (S ω) ≤ β₀ + 1 / ((n : ℝ) + 1) := fun n =>
    theta_le_of_isRegular (by linarith [hpos n]) (hω n)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  linarith [hle n]
end DeletedPrimes
