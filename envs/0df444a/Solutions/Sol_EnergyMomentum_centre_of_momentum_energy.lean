-- Prove2me | solution 1 for EnergyMomentum.centre_of_momentum_energy
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:41:27.173513+00:00
-- url     : https://prove2.me/submissions/52fe617f-a9b8-489a-bb8f-1856fa95d8c6

import Definitions.Def_EnergyMomentum_basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped BigOperators
open EnergyMomentum

theorem solution {ι : Type} (s : Finset ι) (m : ι → ℝ) (v : ι → Vec3)
    (c : ℝ) (hc : 0 < c) (hm : ∀ n ∈ s, 0 < m n) (hv : ∀ n ∈ s, ‖v n‖ < c)
    (hcom : ∑ n ∈ s, momentum (m n) c (v n) = 0) :
    ∑ n ∈ s, energy (m n) c (v n)
      = invariantMass c (∑ n ∈ s, fourMomentum (m n) c (v n)) * c ^ 2 := by
  have hE : 0 ≤ ∑ n ∈ s, energy (m n) c (v n) := by
    apply Finset.sum_nonneg
    intro n hn
    unfold energy lorentzFactor
    exact mul_nonneg (mul_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg _)) (hm n hn).le) (sq_nonneg c)
  have hfirst : (∑ n ∈ s, fourMomentum (m n) c (v n)).1 =
      (∑ n ∈ s, energy (m n) c (v n)) / c := by
    simp [fourMomentum, Prod.fst_sum, Finset.sum_div]
  have hsecond : (∑ n ∈ s, fourMomentum (m n) c (v n)).2 = 0 := by
    simpa [fourMomentum, Prod.snd_sum] using hcom
  rw [invariantMass, minkowskiInner, hfirst, hsecond]
  simp only [inner_zero_left, sub_zero, ← pow_two]
  rw [Real.sqrt_sq (div_nonneg hE hc.le)]
  field_simp [hc.ne']

#print axioms solution
