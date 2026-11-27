-- Prove2me | solution 1 for FiniteTD.Markov.Supplement.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:01.610707+00:00
-- url     : https://prove2.me/submissions/6ab6d7fa-a434-4b73-bf1f-d0f83cea5843

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid

open FiniteTD
open FiniteTD.Markov
open FiniteTD.Markov.Supplement

open scoped InnerProductSpace

theorem solution {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hstar : gbar π P γ Rw φ θstar = 0) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      ‖gbar π P γ Rw φ θ‖ ≤ 2 * Real.sqrt (dNormSq π φ (θ - θstar)) := by
        intro θ
        obtain ⟨hP0, hP1⟩ := hP
        obtain ⟨hπ0, hπ1, hπP⟩ := hπ
        set x := θ - θstar with hx
        set a : S → ℝ := fun s => ⟪φ s, x⟫_ℝ with ha
        have hdiff : gbar π P γ Rw φ θ = ∑ s, ∑ s', (π s * P s s') • ((γ * a s' - a s) • φ s) := by
          rw [← sub_zero (gbar π P γ Rw φ θ), ← hstar]
          unfold gbar
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun s' _ => ?_
          unfold tdDir
          rw [← smul_sub, ← sub_smul]
          congr 2
          simp only [ha, hx, inner_sub_right]
          ring
        have hbound : ‖gbar π P γ Rw φ θ‖ ≤ ∑ s, ∑ s', (π s * P s s') * (|a s'| + |a s|) := by
          rw [hdiff]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s' _ => ?_)
          have hw : 0 ≤ π s * P s s' := mul_nonneg (hπ0 s) (hP0 s s')
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw]
          refine mul_le_mul_of_nonneg_left ?_ hw
          have h1 : |γ * a s' - a s| ≤ |a s'| + |a s| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_of_nonneg hγ0]
            have := mul_le_mul_of_nonneg_right hγ1.le (abs_nonneg (a s'))
            linarith
          calc |γ * a s' - a s| * ‖φ s‖ ≤ |γ * a s' - a s| * 1 :=
                mul_le_mul_of_nonneg_left (hφ s) (abs_nonneg _)
            _ ≤ |a s'| + |a s| := by rw [mul_one]; exact h1
        have hsum : ∑ s, ∑ s', (π s * P s s') * (|a s'| + |a s|) = 2 * ∑ s, π s * |a s| := by
          have e1 : ∑ s, ∑ s', (π s * P s s') * |a s'| = ∑ s, π s * |a s| := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [← Finset.sum_mul, hπP s']
          have e2 : ∑ s, ∑ s', (π s * P s s') * |a s| = ∑ s, π s * |a s| := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [← Finset.sum_mul, ← Finset.mul_sum, hP1 s, mul_one]
          simp only [mul_add, Finset.sum_add_distrib]
          rw [e1, e2]
          ring
        have hjensen : ∑ s, π s * |a s| ≤ Real.sqrt (dNormSq π φ x) := by
          apply Real.le_sqrt_of_sq_le
          set m := ∑ s, π s * |a s| with hm
          have h0 : 0 ≤ ∑ s, π s * (|a s| - m) ^ 2 :=
            Finset.sum_nonneg fun s _ => mul_nonneg (hπ0 s) (sq_nonneg _)
          have h1 : ∑ s, π s * (|a s| - m) ^ 2 = dNormSq π φ x - 2 * m * m + m ^ 2 * 1 := by
            have h2 : ∀ s, π s * (|a s| - m) ^ 2
                = π s * ⟪φ s, x⟫_ℝ ^ 2 - 2 * m * (π s * |a s|) + m ^ 2 * π s := by
              intro s
              have h3 : ⟪φ s, x⟫_ℝ ^ 2 = |a s| ^ 2 := by rw [sq_abs]
              rw [h3]
              ring
            rw [Finset.sum_congr rfl fun s _ => h2 s, Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, hπ1, ← hm]
            rfl
          nlinarith
        calc ‖gbar π P γ Rw φ θ‖ ≤ 2 * ∑ s, π s * |a s| := hbound.trans hsum.le
          _ ≤ 2 * Real.sqrt (dNormSq π φ x) := by linarith
