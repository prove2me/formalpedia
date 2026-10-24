-- Prove2me | solution 1 for EnergyMomentum.system_energy_momentum_relation
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:50:09.134999+00:00
-- url     : https://prove2.me/submissions/a143fd46-2a24-4214-a633-3dd9c651bd08

import Definitions.Def_EnergyMomentum_basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
open EnergyMomentum

theorem solution {ι : Type} (s : Finset ι) (m : ι → ℝ) (v : ι → Vec3)
    (c : ℝ) (hc : 0 < c) (hm : ∀ n ∈ s, 0 < m n) (hv : ∀ n ∈ s, ‖v n‖ < c) :
    (∑ n ∈ s, energy (m n) c (v n)) ^ 2
      = (‖∑ n ∈ s, momentum (m n) c (v n)‖ * c) ^ 2
        + (invariantMass c (∑ n ∈ s, fourMomentum (m n) c (v n)) * c ^ 2) ^ 2 := by
  classical
  let E : ℝ := ∑ n ∈ s, energy (m n) c (v n)
  let p : Vec3 := ∑ n ∈ s, momentum (m n) c (v n)
  let P : FourVec := ∑ n ∈ s, fourMomentum (m n) c (v n)
  have hfactor (n : ι) (hn : n ∈ s) : 0 ≤ lorentzFactor c (v n) * m n :=
    mul_nonneg (by unfold lorentzFactor; exact div_nonneg zero_le_one (Real.sqrt_nonneg _)) (hm n hn).le
  have henergy (n : ι) : energy (m n) c (v n) / c = lorentzFactor c (v n) * m n * c := by
    unfold energy
    field_simp [hc.ne']
  have hbound (n : ι) (hn : n ∈ s) : ‖momentum (m n) c (v n)‖ ≤ energy (m n) c (v n) / c := by
    rw [momentum, norm_smul, Real.norm_of_nonneg (hfactor n hn), henergy]
    exact mul_le_mul_of_nonneg_left (hv n hn).le (hfactor n hn)
  have htotal : ‖p‖ ≤ E / c := by
    calc
      _ ≤ ∑ n ∈ s, ‖momentum (m n) c (v n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ s, energy (m n) c (v n) / c := Finset.sum_le_sum hbound
      _ = _ := by simp only [E, Finset.sum_div]
  have hP1 : P.1 = E / c := by simp [P, Prod.fst_sum, fourMomentum, E, Finset.sum_div]
  have hP2 : P.2 = p := by simp [P, Prod.snd_sum, fourMomentum, p]
  have hrad : 0 ≤ minkowskiInner P P := by
    rw [minkowskiInner, hP1, hP2, real_inner_self_eq_norm_sq]
    have hsq : ‖p‖ ^ 2 ≤ (E / c) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg p) ((norm_nonneg p).trans htotal)).2 htotal
    simpa only [pow_two] using (sub_nonneg.mpr hsq)
  have hmass : (invariantMass c P * c ^ 2) ^ 2 = E ^ 2 - (‖p‖ * c) ^ 2 := by
    have hsqrt := Real.sq_sqrt hrad
    have hcancel : Real.sqrt (minkowskiInner P P) / c * c ^ 2 =
        Real.sqrt (minkowskiInner P P) * c := by
      field_simp [hc.ne']
    rw [invariantMass, hcancel, mul_pow, hsqrt]
    rw [minkowskiInner, hP1, hP2, real_inner_self_eq_norm_sq]
    field_simp [hc.ne']
  change E ^ 2 = (‖p‖ * c) ^ 2 + (invariantMass c P * c ^ 2) ^ 2
  linarith [hmass]

#print axioms solution
