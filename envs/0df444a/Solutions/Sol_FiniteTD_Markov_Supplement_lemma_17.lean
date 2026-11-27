-- Prove2me | solution 1 for FiniteTD.Markov.Supplement.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:54.106943+00:00
-- url     : https://prove2.me/submissions/d75c8745-305b-4322-b0c1-bad88ab857d5

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

open FiniteTD
open FiniteTD.Markov
open FiniteTD.Markov.Supplement

theorem solution {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) :
    ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R →
      (∀ (w : ℕ → S) (t : ℕ),
        ‖tdErr γ Rw φ θ (w t) (w (t + 1)) • traceN φ (γ * lam) w t‖ ≤
          (rmax + 2 * R) / (1 - γ * lam)) ∧
      ‖xbar π P γ lam Rw φ θ‖ ≤ (rmax + 2 * R) / (1 - γ * lam) := by
        intro θ hθ
        have hq0 : 0 ≤ γ * lam := mul_nonneg hγ0 hlam0
        have hq1 : γ * lam < 1 := by nlinarith
        have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hθ
        have hin : ∀ s, |inner ℝ (φ s) θ| ≤ R := by
          intro s
          calc |inner ℝ (φ s) θ| ≤ ‖φ s‖ * ‖θ‖ := abs_real_inner_le_norm _ _
            _ ≤ 1 * R := mul_le_mul (hφ s) hθ (norm_nonneg _) zero_le_one
            _ = R := one_mul R
        have htd : ∀ s s', |tdErr γ Rw φ θ s s'| ≤ rmax + 2 * R := by
          intro s s'
          have h1 := abs_le.mp (hRw s s')
          have h2 := abs_le.mp (hin s)
          have h3 := abs_le.mp (hin s')
          unfold tdErr
          rw [abs_le]
          constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
        have hgeo : HasSum (fun k : ℕ => (γ * lam) ^ k) (1 - γ * lam)⁻¹ :=
          hasSum_geometric_of_lt_one hq0 hq1
        refine ⟨?_, ?_⟩
        · intro w t
          have htr : ‖traceN φ (γ * lam) w t‖ ≤ (1 - γ * lam)⁻¹ := by
            unfold traceN
            calc _ ≤ ∑ k ∈ Finset.range (t + 1), ‖(γ * lam) ^ k • φ (w (t - k))‖ := norm_sum_le _ _
              _ ≤ ∑ k ∈ Finset.range (t + 1), (γ * lam) ^ k := by
                refine Finset.sum_le_sum fun k _ => ?_
                rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hq0 k)]
                exact mul_le_of_le_one_right (pow_nonneg hq0 k) (hφ _)
              _ ≤ _ := sum_le_hasSum _ (fun k _ => pow_nonneg hq0 k) hgeo
          have hC := le_trans (abs_nonneg _) (htd (w t) (w (t + 1)))
          rw [norm_smul, Real.norm_eq_abs, div_eq_mul_inv]
          exact mul_le_mul (htd _ _) htr (norm_nonneg _) hC
        · have hc : ∀ u, |∑ u', P u u' * (Rw u u' + γ * valFn φ θ u' - valFn φ θ u)|
              ≤ rmax + 2 * R := by
            intro u
            calc _ ≤ ∑ u', |P u u' * (Rw u u' + γ * valFn φ θ u' - valFn φ θ u)| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ u', P u u' * (rmax + 2 * R) := by
                refine Finset.sum_le_sum fun u' _ => ?_
                rw [abs_mul, abs_of_nonneg (hP.1 u u')]
                exact mul_le_mul_of_nonneg_left (htd u u') (hP.1 u u')
              _ = rmax + 2 * R := by rw [← Finset.sum_mul, hP.2 u, one_mul]
          have hpow : ∀ (k : ℕ) (c : S → ℝ), (∀ u, |c u| ≤ rmax + 2 * R) →
              ∀ s, |((Matrix.of P ^ k).mulVec c) s| ≤ rmax + 2 * R := by
            intro k
            induction k with
            | zero => intro c h s; simpa using h s
            | succ n ih =>
              intro c h s
              rw [pow_succ, ← Matrix.mulVec_mulVec]
              refine ih _ (fun u => ?_) s
              simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
              calc _ ≤ ∑ u', |P u u' * c u'| := Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ u', P u u' * (rmax + 2 * R) := by
                  refine Finset.sum_le_sum fun u' _ => ?_
                  rw [abs_mul, abs_of_nonneg (hP.1 u u')]
                  exact mul_le_mul_of_nonneg_left (h u') (hP.1 u u')
                _ = rmax + 2 * R := by rw [← Finset.sum_mul, hP.2 u, one_mul]
          have hT : ∀ s, |Tlam P γ lam Rw (valFn φ θ) s - valFn φ θ s|
              ≤ (rmax + 2 * R) / (1 - γ * lam) := by
            intro s
            unfold Tlam
            rw [add_sub_cancel_left, ← Real.norm_eq_abs, div_eq_mul_inv]
            refine tsum_of_norm_bounded (hgeo.mul_left (rmax + 2 * R)) fun k => ?_
            rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hq0 k), mul_comm, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hpow k _ hc s) (pow_nonneg hq0 k)
          unfold xbar gbarH
          calc _ ≤ ∑ s, ‖(π s * (Tlam P γ lam Rw (valFn φ θ) s - valFn φ θ s)) • φ s‖ :=
                norm_sum_le _ _
            _ ≤ ∑ s, π s * ((rmax + 2 * R) / (1 - γ * lam)) := by
              refine Finset.sum_le_sum fun s _ => ?_
              rw [norm_smul, norm_mul, Real.norm_of_nonneg (hπ.1 s), Real.norm_eq_abs]
              have h1 : π s * |Tlam P γ lam Rw (valFn φ θ) s - valFn φ θ s|
                  ≤ π s * ((rmax + 2 * R) / (1 - γ * lam)) :=
                mul_le_mul_of_nonneg_left (hT s) (hπ.1 s)
              exact le_trans (mul_le_of_le_one_right
                (mul_nonneg (hπ.1 s) (abs_nonneg _)) (hφ s)) h1
            _ = _ := by rw [← Finset.sum_mul, hπ.2.1, one_mul]
