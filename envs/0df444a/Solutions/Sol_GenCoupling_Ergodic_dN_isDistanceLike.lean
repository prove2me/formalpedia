-- Prove2me | solution 1 for GenCoupling.Ergodic.dN_isDistanceLike
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:29:15.126207+00:00
-- url     : https://prove2.me/submissions/a30e452f-2c74-4283-98a6-bfebcfdcd2df

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open GenCoupling.Ergodic in
theorem solution {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (θ : E → E → ℝ) (hθ : IsPremetric θ) (N : ℝ) (hN : 0 < N) :
    IsDistanceLike (dN θ N) ∧ (∀ x y, dN θ N x y ≤ 1) ∧ ∀ x y, dN θ N x y ≤ N * θ x y := by
  obtain ⟨hnn, hlsc, hzero⟩ := hθ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x y
    unfold dN
    exact le_min (le_min (mul_nonneg hN.le (hnn x y)) (mul_nonneg hN.le (hnn y x))) zero_le_one
  · intro x y
    unfold dN
    rw [min_comm (N * θ x y)]
  · unfold dN
    have hmono : Monotone (fun u : ℝ => N * u) := fun a b hab => mul_le_mul_of_nonneg_left hab hN.le
    have hc : Continuous (fun u : ℝ => N * u) := continuous_const.mul continuous_id
    have h1 : LowerSemicontinuous (fun p : E × E => N * θ p.1 p.2) :=
      hc.comp_lowerSemicontinuous hlsc hmono
    have hswap : LowerSemicontinuous (fun p : E × E => θ p.2 p.1) :=
      hlsc.comp continuous_swap
    have h2 : LowerSemicontinuous (fun p : E × E => N * θ p.2 p.1) :=
      hc.comp_lowerSemicontinuous hswap hmono
    exact (h1.inf h2).inf lowerSemicontinuous_const
  · intro x y
    unfold dN
    constructor
    · intro h
      have ha := mul_nonneg hN.le (hnn x y)
      have hb := mul_nonneg hN.le (hnn y x)
      have hm : min (N * θ x y) (N * θ y x) = 0 := by
        rcases le_total (min (N * θ x y) (N * θ y x)) 1 with h1 | h1
        · rw [min_eq_left h1] at h; exact h
        · rw [min_eq_right h1] at h; norm_num at h
      rcases min_choice (N * θ x y) (N * θ y x) with h2 | h2
      · rw [h2] at hm
        exact (hzero x y).mp ((mul_eq_zero.mp hm).resolve_left hN.ne')
      · rw [h2] at hm
        exact ((hzero y x).mp ((mul_eq_zero.mp hm).resolve_left hN.ne')).symm
    · rintro rfl
      rw [(hzero x x).mpr rfl]
      simp
  · intro x y
    unfold dN
    exact min_le_right _ _
  · intro x y
    unfold dN
    exact (min_le_left _ _).trans (min_le_left _ _)
