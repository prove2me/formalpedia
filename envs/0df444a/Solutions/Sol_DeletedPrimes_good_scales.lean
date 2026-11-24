-- Prove2me | solution 1 for DeletedPrimes.good_scales
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:12:24.98559+00:00
-- url     : https://prove2.me/submissions/92565459-23c1-426e-8693-6c04c5fb0755

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
import Theorems.Thm_DeletedPrimes_good_scale

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hM : MertensLaw S α m) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {k : ℕ} (lam : Fin k → ℝ)
    (hlam : ∀ i, 0 < lam i) (hsep : ∀ i i' : Fin k, i < i' → lam i * (1 + δ) < lam i') :
    ∀ᶠ X : ℝ in atTop, ∃ j : Fin k → ℕ, StrictMono j ∧ ∀ i,
      X ^ lam i ≤ 2 ^ j i ∧ (2 : ℝ) ^ j i ≤ X ^ (lam i * (1 + δ)) ∧
      ((2 : ℝ) ^ j i) ^ (α - ε) ≤ blockCount S (2 ^ j i) := by
  have hg := good_scale hα hm hM hδ hε
  have hall : ∀ i : Fin k, ∀ᶠ X : ℝ in atTop, ∃ j : ℕ, X ^ lam i ≤ 2 ^ j ∧
      (2 : ℝ) ^ j ≤ (X ^ lam i) ^ (1 + δ) ∧ ((2 : ℝ) ^ j) ^ (α - ε) ≤ blockCount S (2 ^ j) :=
    fun i => (tendsto_rpow_atTop (hlam i)).eventually hg
  filter_upwards [Filter.eventually_all.mpr hall, eventually_gt_atTop 1] with X hX hX1
  choose j hj using hX
  have hX0 : 0 ≤ X := by linarith
  have hj' : ∀ i, X ^ lam i ≤ 2 ^ j i ∧ (2 : ℝ) ^ j i ≤ X ^ (lam i * (1 + δ)) ∧
      ((2 : ℝ) ^ j i) ^ (α - ε) ≤ blockCount S (2 ^ j i) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hj i
    refine ⟨h1, ?_, h3⟩
    rwa [Real.rpow_mul hX0]
  refine ⟨j, fun i i' hii' => ?_, hj'⟩
  have h1 : (2 : ℝ) ^ j i < 2 ^ j i' := by
    calc (2 : ℝ) ^ j i ≤ X ^ (lam i * (1 + δ)) := (hj' i).2.1
      _ < X ^ lam i' := Real.rpow_lt_rpow_of_exponent_lt hX1 (hsep i i' hii')
      _ ≤ 2 ^ j i' := (hj' i').1
  exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h1
end DeletedPrimes
