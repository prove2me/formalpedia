-- Prove2me | solution 1 for BilevelSOC.SecondOrder.Supplement.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:57.511796+00:00
-- url     : https://prove2.me/submissions/dd62ffcf-6876-4d8d-92bf-a6a9dbd01134

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_FirstOrder
open scoped Topology

open BilevelSOC
open BilevelSOC.SecondOrder
open BilevelSOC.SecondOrder.Supplement

theorem solution {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hexclude : ∀ d ∈ tangentCone (feasSet D) z, fderiv ℝ D.F z d ≤ 0 → d = 0) :
    GrowthCondition D.F (feasSet D) z 1 ∧ StrictLocalMin D.F (feasSet D) z := by
      have hdiff : HasFDerivAt D.F (fderiv ℝ D.F z) z :=
        (hStanding.1.differentiable (by norm_num) z).hasFDerivAt
      have key : GrowthCondition D.F (feasSet D) z 1 := by
        refine ⟨hfeas, ?_⟩
        by_contra hcon
        have hseq : ∀ k : ℕ, ∃ a ∈ feasSet D, ‖a - z‖ < 1 / ((k : ℝ) + 1) ∧
            D.F a < D.F z + 1 / ((k : ℝ) + 1) * ‖a - z‖ := by
          intro k
          by_contra hk
          push Not at hk
          have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          refine hcon ⟨Metric.ball z (1 / ((k : ℝ) + 1)), Metric.ball_mem_nhds z hpos,
            1 / ((k : ℝ) + 1), hpos, ?_⟩
          rintro a ⟨haX, haU⟩
          rw [Real.rpow_one]
          exact hk a haX (by rwa [Metric.mem_ball, dist_eq_norm] at haU)
        choose a haX haN haF using hseq
        have hne : ∀ k, 0 < ‖a k - z‖ := by
          intro k
          rcases (norm_nonneg (a k - z)).lt_or_eq with h | h
          · exact h
          · exfalso
            have h1 : a k = z := by
              rw [← sub_eq_zero, ← norm_eq_zero]; exact h.symm
            have h2 := haF k
            rw [h1] at h2
            simp at h2
        have hone : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have ht0 : Filter.Tendsto (fun k => ‖a k - z‖) Filter.atTop (𝓝 0) :=
          squeeze_zero (fun k => norm_nonneg _) (fun k => (haN k).le) hone
        have hu : ∀ k, ‖a k - z‖⁻¹ • (a k - z) ∈ Metric.sphere (0 : E n × Y m) 1 := by
          intro k
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
          exact inv_mul_cancel₀ (hne k).ne'
        obtain ⟨d, hd, φ, hφ, hlim⟩ :=
          (isCompact_sphere (0 : E n × Y m) 1).tendsto_subseq hu
        have hlim' : Filter.Tendsto (fun k => ‖a (φ k) - z‖⁻¹ • (a (φ k) - z))
            Filter.atTop (𝓝 d) := hlim
        have ht0' : Filter.Tendsto (fun k => ‖a (φ k) - z‖) Filter.atTop (𝓝 0) :=
          ht0.comp hφ.tendsto_atTop
        have hdT : d ∈ tangentCone (feasSet D) z := by
          refine ⟨fun k => ‖a (φ k) - z‖, fun k => ‖a (φ k) - z‖⁻¹ • (a (φ k) - z),
            fun k => hne _, ht0', hlim', ?_⟩
          intro k
          have h1 : z + ‖a (φ k) - z‖ • ‖a (φ k) - z‖⁻¹ • (a (φ k) - z) = a (φ k) := by
            rw [smul_smul, mul_inv_cancel₀ (hne _).ne', one_smul, add_sub_cancel]
          show z + ‖a (φ k) - z‖ • ‖a (φ k) - z‖⁻¹ • (a (φ k) - z) ∈ feasSet D
          rw [h1]
          exact haX _
        have hz0 : Filter.Tendsto (fun k => a (φ k) - z) Filter.atTop (𝓝 0) :=
          tendsto_zero_iff_norm_tendsto_zero.2 ht0'
        have hF : Filter.Tendsto
            (fun k => ‖a (φ k) - z‖⁻¹ • (D.F (z + (a (φ k) - z)) - D.F z))
            Filter.atTop (𝓝 (fderiv ℝ D.F z d)) :=
          (hdiff.hasFDerivWithinAt (s := Set.univ)).lim hz0
            (Filter.Eventually.of_forall fun k => Set.mem_univ _) hlim'
        have hle : fderiv ℝ D.F z d ≤ 0 := by
          refine le_of_tendsto_of_tendsto' hF (hone.comp hφ.tendsto_atTop) fun k => ?_
          have h1 := haF (φ k)
          rw [add_sub_cancel, smul_eq_mul, inv_mul_le_iff₀ (hne _)]
          simp only [Function.comp]
          linarith [mul_comm ‖a (φ k) - z‖ (1 / (((φ k : ℕ) : ℝ) + 1))]
        have hd0 := hexclude d hdT hle
        rw [hd0] at hd
        simp at hd
      refine ⟨key, hfeas, ?_⟩
      obtain ⟨_, U, hU, C, hC, hg⟩ := key
      refine ⟨U, hU, fun a ha hne => ?_⟩
      have h1 := hg a ha
      rw [Real.rpow_one] at h1
      have h2 : 0 < C * ‖a - z‖ := mul_pos hC (norm_pos_iff.2 (sub_ne_zero.2 hne))
      linarith
