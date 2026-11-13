-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a59_original_pathwise_uniform_C2_mesh_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:26:31.65778+00:00
-- url     : https://prove2.me/submissions/73258c67-e989-4407-99a8-adda7aa8271b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem solution
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mOmega}
    (X : SpectrallyNegativeLevy P F)
    (x : Real) (D : NNReal -> Omega -> Real)
    (hD : IsDividendStrategy F D)
    (C : ENNReal) (w : Real -> Real)
    (hw : ContDiffOn Real 2 w {z : Real | 0 < z ∧ ENNReal.ofReal z < C})
    (a b : Real) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (omega : Omega) (S : Nat -> Finset Nat)
    (s : Nat -> Nat -> NNReal) (y : Nat -> Nat -> Real)
    (K : Real) (hK : 0 ≤ K) :
    let z : Nat -> Nat -> Real := fun m i =>
      x + X.X (s m i) omega - rightLimit D (s m i) omega
    (∀ m i, i ∈ S m -> z m i ∈ Icc a b ∧
      y m i ∈ Icc a b ∧ z m i ≠ y m i) ->
    (∀ delta : Real, 0 < delta -> ∃ k : Nat,
      ∀ m : Nat, k ≤ m -> ∀ i ∈ S m,
        dist (y m i) (z m i) < delta) ->
    (∀ m : Nat, (∑ i ∈ S m, (y m i - z m i) ^ 2) ≤ K) ->
    ∀ eps : Real, 0 < eps -> ∃ k : Nat,
      ∀ m : Nat, k ≤ m ->
      |∑ i ∈ S m, (w (y m i) -
        taylorWithinEval w 1 (uIcc (z m i) (y m i)) (z m i) (y m i) -
        (iteratedDeriv 2 w (z m i) * (y m i - z m i) ^ 2) / 2)| ≤ eps := by
  intro z hInside hGap hEnergy eps heps
  have hKone : 0 < K + 1 := by linarith only [hK]
  have hsmall : 0 < eps / (K + 1) := div_pos heps hKone
  obtain ⟨ delta, hdelta, hTaylor ⟩ :=
    avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
      X x D hD C w hw a b ha hab hbcap
      (eps / (K + 1)) hsmall
  obtain ⟨ k, hk ⟩ := hGap delta hdelta
  refine ⟨ k, ?_ ⟩
  intro m hm
  have hReq : ∀ i ∈ S m,
      (x + X.X (s m i) omega - rightLimit D (s m i) omega) ∈ Icc a b ∧
      y m i ∈ Icc a b ∧
      (x + X.X (s m i) omega - rightLimit D (s m i) omega) ≠ y m i ∧
      dist (y m i) (x + X.X (s m i) omega -
        rightLimit D (s m i) omega) < delta := by
    intro i hi
    obtain ⟨ hbz, hby, hneq ⟩ := hInside m i hi
    exact ⟨ hbz, hby, hneq, hk m hm i hi ⟩
  have hTaylorBound := hTaylor omega (S m) (s m) (y m) hReq
  have hBound : |∑ i ∈ S m, (w (y m i) -
      taylorWithinEval w 1 (uIcc (z m i) (y m i)) (z m i) (y m i) -
      (iteratedDeriv 2 w (z m i) * (y m i - z m i) ^ 2) / 2)| ≤
      (eps / (K + 1)) * (∑ i ∈ S m, (y m i - z m i) ^ 2) := by
    simpa only [z] using hTaylorBound
  calc
    |∑ i ∈ S m, (w (y m i) -
        taylorWithinEval w 1 (uIcc (z m i) (y m i)) (z m i) (y m i) -
        (iteratedDeriv 2 w (z m i) * (y m i - z m i) ^ 2) / 2)|
        ≤ (eps / (K + 1)) * (∑ i ∈ S m, (y m i - z m i) ^ 2) := hBound
    _ ≤ (eps / (K + 1)) * K :=
      mul_le_mul_of_nonneg_left (hEnergy m) (le_of_lt hsmall)
    _ ≤ eps := by
      calc
        (eps / (K + 1)) * K = eps * K / (K + 1) := by ring
        _ ≤ eps := (div_le_iff₀ hKone).2 (by nlinarith only [heps.le])
