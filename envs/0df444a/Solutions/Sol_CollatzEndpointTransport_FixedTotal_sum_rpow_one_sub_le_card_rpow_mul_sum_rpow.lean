-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_rpow_one_sub_le_card_rpow_mul_sum_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:03.987217+00:00
-- url     : https://prove2.me/submissions/52b3f1f6-e8d7-4d9c-b308-39d66141d39c

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {ι : Type*} (U : Finset ι) (p : ι → ℝ)
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hp : ∀ i ∈ U, 0 ≤ p i) :
    ∑ i ∈ U, (p i) ^ (1 - theta) ≤
      (U.card : ℝ) ^ theta * (∑ i ∈ U, p i) ^ (1 - theta) := by
  by_cases hU : U = ∅
  · simp [hU, Real.zero_rpow htheta0.ne']
  have hcardNat : 0 < U.card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU)
  have hcard : 0 < (U.card : ℝ) := Nat.cast_pos.mpr hcardNat
  let w : ι → ℝ := fun _ => (U.card : ℝ)⁻¹
  let q : ι → ℝ := fun i => (U.card : ℝ) * p i
  have hwsum : ∑ i ∈ U, w i = 1 := by
    simp [w, hcard.ne']
  have hw0 : ∀ i ∈ U, 0 ≤ w i := by
    intro i hi
    dsimp [w]
    positivity
  have hqmem : ∀ i ∈ U, q i ∈ Set.Ici (0 : ℝ) := by
    intro i hi
    exact Set.mem_Ici.mpr (mul_nonneg hcard.le (hp i hi))
  have hconc := Real.concaveOn_rpow
    (p := 1 - theta) (by linarith) (by linarith)
  have hj := hconc.le_map_sum hw0 hwsum hqmem
  have hleft :
      ∑ i ∈ U, w i • ((q i) ^ (1 - theta)) =
        (U.card : ℝ) ^ (-theta) *
          ∑ i ∈ U, (p i) ^ (1 - theta) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_eq_mul]
    dsimp [w, q]
    rw [Real.mul_rpow hcard.le (hp i hi)]
    rw [Real.rpow_one_sub' hcard.le (by linarith : 1 - theta ≠ 0)]
    rw [Real.rpow_neg hcard.le]
    field_simp [hcard.ne', (Real.rpow_pos_of_pos hcard _).ne']
  have hright :
      (∑ i ∈ U, w i • q i) ^ (1 - theta) =
        (∑ i ∈ U, p i) ^ (1 - theta) := by
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_eq_mul]
    dsimp [w, q]
    field_simp [hcard.ne']
  rw [hleft, hright] at hj
  have hpowPos : 0 < (U.card : ℝ) ^ (-theta) :=
    Real.rpow_pos_of_pos hcard _
  have hdiv :
      ∑ i ∈ U, (p i) ^ (1 - theta) ≤
        (∑ i ∈ U, p i) ^ (1 - theta) /
          (U.card : ℝ) ^ (-theta) :=
    (le_div_iff₀ hpowPos).2 (by simpa [mul_comm] using hj)
  calc
    ∑ i ∈ U, (p i) ^ (1 - theta) ≤
        (∑ i ∈ U, p i) ^ (1 - theta) /
          (U.card : ℝ) ^ (-theta) := hdiv
    _ = (U.card : ℝ) ^ theta *
          (∑ i ∈ U, p i) ^ (1 - theta) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hcard.le]
      ring_nf
end CollatzEndpointTransport.FixedTotal
