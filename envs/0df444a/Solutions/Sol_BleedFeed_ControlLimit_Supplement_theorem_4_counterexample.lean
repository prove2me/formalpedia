-- Prove2me | solution 1 for BleedFeed.ControlLimit.Supplement.theorem_4_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:37.167035+00:00
-- url     : https://prove2.me/submissions/bdc8245d-83a5-4a14-96c5-ffaa5a2ddd51

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Supplement_RegulatoryValue

open BleedFeed
open BleedFeed.ControlLimit
open BleedFeed.ControlLimit.Supplement

/-- Counterexample to Theorem 4's printed limit and to Remark 3's proposed repair
    on the full §3 domain: I = 1 allows no further reward before mandatory harvest. -/
theorem solution :
    let P : Params := {
      m0 := 1, tau := 1, muL := 1, muU := 1, mtil := 3 / 2,
      nu := fun m => 1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹,
      I := 1, N := 0, G := MeasureTheory.Measure.dirac 1 }
    P.Standing ∧ critAge P 1 = 1 ∧
      P.G {μ | 0 < critAge P μ} = 1 ∧
      (∀ N : ℕ, F P N = 1) ∧ (∀ N : ℕ, increment P N = 0) ∧
      criticalReward P = 1 ∧
      ¬ Filter.Tendsto (increment P) Filter.atTop (nhds P.mtil) ∧
      ¬ Filter.Tendsto (increment P) Filter.atTop (nhds (criticalReward P)) := by
        intro P
        have hz : ∀ m : ℝ, m ≤ 3 / 2 → (1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹ : ℝ) = 0 := by
          intro m hm
          simp [max_eq_right (sub_nonpos.mpr hm)]
        have hs : StrictMonoOn (fun m : ℝ => 1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹) (Set.Ici (3 / 2)) := by
          intro a ha b hb hab
          have ha' : 0 ≤ a - 3 / 2 := sub_nonneg.mpr ha
          have hb' : 0 ≤ b - 3 / 2 := sub_nonneg.mpr hb
          dsimp only
          rw [max_eq_left ha', max_eq_left hb']
          have hpos : 0 < 1 + 18 * (a - 3 / 2) := by linarith
          have hlt : 1 + 18 * (a - 3 / 2) < 1 + 18 * (b - 3 / 2) := by linarith
          have h := (inv_lt_inv₀ (by linarith : 0 < 1 + 18 * (b - 3 / 2)) hpos).2 hlt
          linarith
        have hu : ∀ m : ℝ, (1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹ : ℝ) ≤ 1 := by
          intro m
          have hp : 0 ≤ (1 + 18 * max (m - 3 / 2) 0)⁻¹ :=
            inv_nonneg.mpr (by nlinarith [le_max_right (m - 3 / 2) 0])
          linarith
        have hm : Measurable (fun m : ℝ => 1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹) := by
          have hc : Continuous (fun m : ℝ => 1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹) := by
            apply Continuous.sub continuous_const
            apply Continuous.inv₀
            · fun_prop
            · intro m
              have : 0 < 1 + 18 * max (m - 3 / 2) 0 := by
                nlinarith [le_max_right (m - 3 / 2) 0]
              exact ne_of_gt this
          exact hc.measurable
        have hstand : P.Standing := by
          refine ⟨by norm_num [P], by norm_num [P], by norm_num [P],
            by norm_num [P], by norm_num [P], by norm_num [P], hz, hs, ?_, hm, ?_, ?_⟩
          · simpa [P] using hu
          · dsimp [P]; infer_instance
          · simp [P, Params.rates]
        have hcrit : ∀ μ : ℝ, 1 ≤ μ → critAge P μ = 1 := by
          intro μ hμ
          unfold critAge
          apply le_antisymm
          · apply Nat.sInf_le
            simp only [Set.mem_ofPred_eq, mass, P, pow_one, one_mul, mul_one]
            linarith
          · apply le_csInf
            · exact ⟨1, by simp [mass, P]; linarith⟩
            · intro n hn
              by_contra h
              have hn0 : n = 0 := by omega
              subst n
              norm_num [mass, P] at hn
        have hF : ∀ N : ℕ, F P N = 1 := by
          intro N
          let Q := withLimit P N
          have hw (b : ℝ) : W Q b 1 1 = 0 := by
            rw [W.eq_def]; simp [Q, withLimit, P]
          have hc (b : ℝ) : Ck Q b 0 1 = 1 := by
            unfold Ck
            rw [hw]
            norm_num [r, mass, Q, withLimit, P]
          have hb (k : ℕ) : Bk Q k ≤ 1 := by
            cases k with
            | zero => norm_num [Bk]
            | succ k =>
              rw [Bk]
              change (∫ μ, Ck Q (Bk Q k) 0 μ ∂MeasureTheory.Measure.dirac 1) ≤ 1
              rw [MeasureTheory.integral_dirac, hc]
          unfold F
          change (∫ μ, v Q 0 μ 0 ∂MeasureTheory.Measure.dirac 1) = 1
          rw [MeasureTheory.integral_dirac]
          simp only [v, B, Nat.sub_zero]
          rw [W.eq_def]
          have hI : ¬ Q.I ≤ 0 := by norm_num [Q, withLimit, P]
          simp only [hI, if_false]
          change max (Ck Q (Bk Q N) 0 1) (Bk Q N) = 1
          rw [hc, max_eq_left (hb N)]
        have hinc : ∀ N : ℕ, increment P N = 0 := by
          intro N; simp [increment, hF]
        have hcr : criticalReward P = 1 := by
          unfold criticalReward
          change (∫ μ, ∑ j ∈ Finset.range (critAge P μ), r P j μ ∂MeasureTheory.Measure.dirac 1) = 1
          rw [MeasureTheory.integral_dirac, hcrit 1 le_rfl]
          norm_num [r, mass, P]
        have hG : P.G {μ | 0 < critAge P μ} = 1 := by
          change MeasureTheory.Measure.dirac (1:ℝ) {μ | 0 < critAge P μ} = 1
          rw [MeasureTheory.Measure.dirac_apply_of_mem]
          simp [hcrit 1 le_rfl]
        have hT : Filter.Tendsto (increment P) Filter.atTop (nhds 0) := by
          have : increment P = fun _ => 0 := funext hinc
          rw [this]; exact tendsto_const_nhds
        refine ⟨hstand, hcrit 1 le_rfl, hG, hF, hinc, hcr, ?_, ?_⟩
        · intro h
          have := tendsto_nhds_unique hT h
          norm_num [P] at this
        · intro h
          have := tendsto_nhds_unique hT h
          rw [hcr] at this
          norm_num at this
