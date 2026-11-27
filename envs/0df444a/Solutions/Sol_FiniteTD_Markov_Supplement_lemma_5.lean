-- Prove2me | solution 1 for FiniteTD.Markov.Supplement.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:30.259729+00:00
-- url     : https://prove2.me/submissions/84058a00-b69e-4533-8e44-64908cc14e08

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid

open FiniteTD
open FiniteTD.Markov
open FiniteTD.Markov.Supplement

theorem solution {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hstar : gbar π P γ Rw φ θstar = 0) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      tupleExp π P (fun s s' => ‖tdDir γ Rw φ θ s s'‖ ^ 2) ≤
        2 * sigmaSq π P γ Rw φ θstar + 8 * dNormSq π φ (θ - θstar) := by
          intro θ
          set u := θ - θstar with hu
          have hpt : ∀ s s', ‖tdDir γ Rw φ θ s s'‖ ^ 2 ≤
              2 * ‖tdDir γ Rw φ θstar s s'‖ ^ 2 + 4 * (inner ℝ (φ s') u) ^ 2 + 4 * (inner ℝ (φ s) u) ^ 2 := by
            intro s s'
            have hθ : θ = θstar + u := by rw [hu]; abel
            have hdec : tdDir γ Rw φ θ s s' = tdDir γ Rw φ θstar s s' +
                (γ * inner ℝ (φ s') u - inner ℝ (φ s) u) • φ s := by
              unfold tdDir
              rw [hθ, inner_add_right, inner_add_right, ← add_smul]
              congr 1; ring
            rw [hdec]
            set c := γ * inner ℝ (φ s') u - inner ℝ (φ s) u
            have h1 := norm_add_le (tdDir γ Rw φ θstar s s') (c • φ s)
            have h2 : ‖c • φ s‖ ≤ |c| := by
              rw [norm_smul, Real.norm_eq_abs]
              have := hφ s
              have := abs_nonneg c
              nlinarith
            have hc : c ^ 2 ≤ 2 * (inner ℝ (φ s') u) ^ 2 + 2 * (inner ℝ (φ s) u) ^ 2 := by
              have hg2 : γ ^ 2 ≤ 1 := by nlinarith
              have := sq_nonneg (inner ℝ (φ s') u)
              have := sq_nonneg (γ * inner ℝ (φ s') u + inner ℝ (φ s) u)
              have : (γ * inner ℝ (φ s') u) ^ 2 ≤ (inner ℝ (φ s') u) ^ 2 := by
                rw [mul_pow]; nlinarith
              simp only [c]; nlinarith
            have hn0 := norm_nonneg (tdDir γ Rw φ θstar s s')
            have hn1 := norm_nonneg (c • φ s)
            have habs : |c| ^ 2 = c ^ 2 := sq_abs c
            have : ‖tdDir γ Rw φ θstar s s' + c • φ s‖ ^ 2 ≤ (‖tdDir γ Rw φ θstar s s'‖ + ‖c • φ s‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
            have : ‖c • φ s‖ ^ 2 ≤ |c| ^ 2 := pow_le_pow_left₀ hn1 h2 2
            nlinarith [sq_nonneg (‖tdDir γ Rw φ θstar s s'‖ - ‖c • φ s‖)]
          have hw : ∀ s s', 0 ≤ π s * P s s' := fun s s' => mul_nonneg (hπ.1 s) (hP.1 s s')
          calc tupleExp π P (fun s s' => ‖tdDir γ Rw φ θ s s'‖ ^ 2)
              ≤ ∑ s, ∑ s', π s * P s s' * (2 * ‖tdDir γ Rw φ θstar s s'‖ ^ 2 + 4 * (inner ℝ (φ s') u) ^ 2
                  + 4 * (inner ℝ (φ s) u) ^ 2) := by
                unfold tupleExp
                apply Finset.sum_le_sum; intro s _
                apply Finset.sum_le_sum; intro s' _
                exact mul_le_mul_of_nonneg_left (hpt s s') (hw s s')
            _ = 2 * sigmaSq π P γ Rw φ θstar + 4 * (∑ s, ∑ s', π s * P s s' * (inner ℝ (φ s') u) ^ 2)
                  + 4 * (∑ s, π s * (inner ℝ (φ s) u) ^ 2 * ∑ s', P s s') := by
                unfold sigmaSq tupleExp
                simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
                congr 1; congr 1
                · apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro s' _; ring
                · apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro s' _; ring
                · apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro s' _; ring
            _ = 2 * sigmaSq π P γ Rw φ θstar + 8 * dNormSq π φ u := by
                have e1 : ∑ s, ∑ s', π s * P s s' * (inner ℝ (φ s') u) ^ 2 = dNormSq π φ u := by
                  unfold dNormSq
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro s' _
                  rw [← hπ.2.2 s', Finset.sum_mul]
                have e2 : ∑ s, π s * (inner ℝ (φ s) u) ^ 2 * ∑ s', P s s' = dNormSq π φ u := by
                  unfold dNormSq
                  apply Finset.sum_congr rfl; intro s _
                  rw [hP.2 s, mul_one]
                rw [e1, e2]; ring
