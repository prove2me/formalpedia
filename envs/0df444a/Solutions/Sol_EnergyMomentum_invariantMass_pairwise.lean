-- Prove2me | solution 1 for EnergyMomentum.invariantMass_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:41:23.621792+00:00
-- url     : https://prove2.me/submissions/5586dd8b-68ff-48b7-8e39-3ee00357f5c4

import Definitions.Def_EnergyMomentum_basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
open EnergyMomentum

private lemma single_mass (m c : ℝ) (v : Vec3) (hc : 0 < c) (hm : 0 < m)
    (hv : ‖v‖ < c) : energy m c v ^ 2 - c ^ 2 * inner ℝ (momentum m c v) (momentum m c v) = (m*c^2)^2 := by
  have hr0 : 0 ≤ ‖v‖ / c := div_nonneg (norm_nonneg _) hc.le
  have hr1 : ‖v‖ / c < 1 := (div_lt_one hc).mpr hv
  have hpos : 0 < 1 - (‖v‖ / c) ^ 2 := by nlinarith
  have hgpos : 0 < lorentzFactor c v := by
    unfold lorentzFactor
    exact one_div_pos.mpr (Real.sqrt_pos.2 hpos)
  have hgsq : lorentzFactor c v ^ 2 * (1 - (‖v‖ / c) ^ 2) = 1 := by
    unfold lorentzFactor
    rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
    exact div_mul_cancel₀ 1 (ne_of_gt hpos)
  have hid : lorentzFactor c v ^ 2 * (c ^ 2 - ‖v‖ ^ 2) = c ^ 2 := by
    field_simp [hc.ne'] at hgsq
    nlinarith only [hgsq]
  have hnorm : ‖momentum m c v‖ = lorentzFactor c v * m * ‖v‖ := by
    simp only [momentum, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hgpos hm)]
  rw [real_inner_self_eq_norm_sq, hnorm, energy]
  linear_combination (m^2*c^2)*hid

private lemma symmetric_pairs {N : ℕ} (F : Fin N → Fin N → ℝ) (hs : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) = (∑ i, F i i) + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, F i j := by
  classical
  have hpoint (i j : Fin N) : F i j =
      (if i < j then F i j else 0) + (if j < i then F i j else 0) + (if i = j then F i i else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h, h.ne, h.not_gt]
    · subst j; simp
    · simp [h, h.ne', h.not_gt]
  have hswap : (∑ i, ∑ j, if j < i then F i j else 0) =
      ∑ i, ∑ j, if i < j then F i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  have hdiag : (∑ i, ∑ j, if i = j then F i i else 0) = ∑ i, F i i := by simp
  have hupper : (∑ i, ∑ j, if i < j then F i j else 0) =
      ∑ i, ∑ j ∈ Finset.Ioi i, F i j := by
    simp_rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
  calc
    (∑ i, ∑ j, F i j) = ∑ i, ∑ j,
        ((if i < j then F i j else 0) + (if j < i then F i j else 0) + (if i = j then F i i else 0)) := by
      apply Finset.sum_congr rfl; intro i _
      exact Finset.sum_congr rfl (fun j _ => hpoint i j)
    _ = (∑ i, ∑ j, if i < j then F i j else 0) +
        (∑ i, ∑ j, if j < i then F i j else 0) + (∑ i, ∑ j, if i = j then F i i else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hswap, hdiag, hupper]; ring

theorem solution (N : ℕ) (m : Fin N → ℝ) (v : Fin N → Vec3)
    (c : ℝ) (hc : 0 < c) (hm : ∀ n, 0 < m n) (hv : ∀ n, ‖v n‖ < c) :
    (invariantMass c (∑ n, fourMomentum (m n) c (v n)) * c ^ 2) ^ 2
        - ∑ n, (m n * c ^ 2) ^ 2
      = 2 * ∑ n, ∑ k ∈ Finset.Ioi n,
          (energy (m n) c (v n) * energy (m k) c (v k)
            - c ^ 2 * inner ℝ (momentum (m n) c (v n)) (momentum (m k) c (v k))) := by
  classical
  let E : ℝ := ∑ n, energy (m n) c (v n)
  let p : Vec3 := ∑ n, momentum (m n) c (v n)
  let P : FourVec := ∑ n, fourMomentum (m n) c (v n)
  have hfactor (n : Fin N) : 0 ≤ lorentzFactor c (v n) * m n :=
    mul_nonneg (by unfold lorentzFactor; exact div_nonneg zero_le_one (Real.sqrt_nonneg _)) (hm n).le
  have henergy (n : Fin N) : energy (m n) c (v n) / c = lorentzFactor c (v n) * m n * c := by
    unfold energy; field_simp [hc.ne']
  have hbound (n : Fin N) : ‖momentum (m n) c (v n)‖ ≤ energy (m n) c (v n) / c := by
    rw [momentum, norm_smul, Real.norm_of_nonneg (hfactor n), henergy]
    exact mul_le_mul_of_nonneg_left (hv n).le (hfactor n)
  have htotal : ‖p‖ ≤ E / c := by
    calc
      _ ≤ ∑ n, ‖momentum (m n) c (v n)‖ := norm_sum_le _ _
      _ ≤ ∑ n, energy (m n) c (v n) / c := Finset.sum_le_sum (fun n _ => hbound n)
      _ = _ := by simp only [E, Finset.sum_div]
  have hP1 : P.1 = E / c := by simp [P, Prod.fst_sum, fourMomentum, E, Finset.sum_div]
  have hP2 : P.2 = p := by simp [P, Prod.snd_sum, fourMomentum, p]
  have hrad : 0 ≤ minkowskiInner P P := by
    rw [minkowskiInner, hP1, hP2, real_inner_self_eq_norm_sq]
    have hsq : ‖p‖ ^ 2 ≤ (E / c) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg p) ((norm_nonneg p).trans htotal)).2 htotal
    simpa only [pow_two] using (sub_nonneg.mpr hsq)
  have hmass : (invariantMass c P * c ^ 2) ^ 2 = E ^ 2 - c ^ 2 * inner ℝ p p := by
    have hcancel : Real.sqrt (minkowskiInner P P) / c * c ^ 2 = Real.sqrt (minkowskiInner P P) * c := by
      field_simp [hc.ne']
    rw [invariantMass, hcancel, mul_pow, Real.sq_sqrt hrad, minkowskiInner, hP1, hP2]
    field_simp [hc.ne']
  let F : Fin N → Fin N → ℝ := fun n k => energy (m n) c (v n) * energy (m k) c (v k) -
    c ^ 2 * inner ℝ (momentum (m n) c (v n)) (momentum (m k) c (v k))
  have hF : ∀ n k, F n k = F k n := by
    intro n k; dsimp [F]; rw [real_inner_comm]; ring
  have hsum : E ^ 2 - c ^ 2 * inner ℝ p p = ∑ n, ∑ k, F n k := by
    simp only [E, p, F, pow_two, inner_sum, sum_inner,
      Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1 <;> rw [Finset.sum_comm]
  have hdiag : (∑ n, F n n) = ∑ n, (m n * c ^ 2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n _
    simpa only [F, pow_two] using single_mass (m n) c (v n) hc (hm n) (hv n)
  change (invariantMass c P * c ^ 2) ^ 2 - ∑ n, (m n * c ^ 2) ^ 2 =
    2 * ∑ n, ∑ k ∈ Finset.Ioi n, F n k
  rw [hmass, hsum, symmetric_pairs F hF, hdiag]
  ring

#print axioms solution
