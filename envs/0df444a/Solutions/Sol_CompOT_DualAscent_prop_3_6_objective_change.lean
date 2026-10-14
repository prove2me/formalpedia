-- Prove2me | solution 1 for CompOT.DualAscent.prop_3_6_objective_change
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-13T21:24:31.270741+00:00
-- url     : https://prove2.me/submissions/25c638f9-0a14-42bd-a87e-8e6ff60cec4b

import Mathlib
import Definitions.Def_CompOT_DualAscent_Defs

theorem solution {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) (S : Finset (Fin n)) (S' : Finset (Fin m)) (ε : ℝ) :
    CompOT.Duality.dualObj a b (f + ε • CompOT.DualAscent.indicatorVec S)
        (g - ε • CompOT.DualAscent.indicatorVec S') - CompOT.Duality.dualObj a b f g
      = ε * (∑ i ∈ S, a i - ∑ j ∈ S', b j) := by
  have h1 : ∑ i, ε * CompOT.DualAscent.indicatorVec S i * a i = ε * ∑ i ∈ S, a i := by
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
    have h2 : ∑ x ∈ Finset.univ.filter (fun x => x ∈ S), ε * CompOT.DualAscent.indicatorVec S x * a x
        = ∑ i ∈ S, ε * a i := by
      rw [show Finset.univ.filter (fun x => x ∈ S) = S by ext; simp]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [CompOT.DualAscent.indicatorVec, hi]
    have h3 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ S), ε * CompOT.DualAscent.indicatorVec S x * a x = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      simp [CompOT.DualAscent.indicatorVec] at hi ⊢
      simp [hi]
    have h4 : ∑ x ∈ Finset.univ.filter (fun x => x ∈ S), ε * a x = ∑ i ∈ S, ε * a i := by
      rw [show Finset.univ.filter (fun x => x ∈ S) = S by ext; simp]
    rw [h2, h3, add_zero]
  have h1' : ∑ j, ε * CompOT.DualAscent.indicatorVec S' j * b j = ε * ∑ j ∈ S', b j := by
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S')]
    have h2 : ∑ x ∈ Finset.univ.filter (fun x => x ∈ S'), ε * CompOT.DualAscent.indicatorVec S' x * b x
        = ∑ i ∈ S', ε * b i := by
      rw [show Finset.univ.filter (fun x => x ∈ S') = S' by ext; simp]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [CompOT.DualAscent.indicatorVec, hi]
    have h3 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ S'), ε * CompOT.DualAscent.indicatorVec S' x * b x = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      simp [CompOT.DualAscent.indicatorVec] at hi ⊢
      simp [hi]
    rw [h2, h3, add_zero]
  unfold CompOT.Duality.dualObj
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h1']
  ring
