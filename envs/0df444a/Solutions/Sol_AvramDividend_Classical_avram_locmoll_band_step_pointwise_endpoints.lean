-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_step_pointwise_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:14:14.964781+00:00
-- url     : https://prove2.me/submissions/f0bfbca0-3749-4873-97b6-38558374eb5e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_clipped_selected_tags_limit
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_cell_endpoint_limits
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H θ : ℝ≥0) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (a b c : ℕ → ℝ → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (htθ : t ≤ (θ : ℝ))
    (he : t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω)
    (h0 : ∀ n, t = 0 → a n t = x ∧ b n t = x - rightLimit D 0 ω ∧ c n t = 1)
    (hpos : ∀ n, 0 < t → ∃ i < m n + 1,
      let l := min ((i : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ
      let r := min (((i + 1 : ℕ) : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ
      (l : ℝ) < t ∧ t ≤ (r : ℝ) ∧
      a n t = x + X.X r ω - rightLimit D l ω ∧
      b n t = (if r = θ ∧ ¬ (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω)
        then riskProcess X x D r ω else x + X.X r ω - rightLimit D r ω) ∧
      c n t = Real.exp (-(q * (r : ℝ)))) :
    Tendsto (fun n => a n t) atTop (𝓝 (riskProcess X x D t.toNNReal ω)) ∧
    Tendsto (fun n => b n t) atTop (𝓝 (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω)) ∧
    Tendsto (fun n => c n t) atTop (𝓝 (Real.exp (-(q * t)))) := by 
  by_cases hz : t = 0
  · subst t
    have ha : (fun n => a n 0) = fun _ => x := funext (fun n => (h0 n rfl).1)
    have hb : (fun n => b n 0) = fun _ => x - rightLimit D 0 ω := funext (fun n => (h0 n rfl).2.1)
    have hc : (fun n => c n 0) = fun _ => 1 := funext (fun n => (h0 n rfl).2.2)
    simp only [ha, hb, hc, Real.toNNReal_zero, X.X_zero, hD.1 ω, riskProcess, add_zero, sub_zero, mul_zero, neg_zero, Real.exp_zero]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds⟩
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    choose i hi hc using fun n => hpos n hp
    have htcoe : (t.toNNReal : ℝ) = t := Real.coe_toNNReal _ ht
    have htθ' : t.toNNReal ≤ θ := by exact_mod_cast (show (t.toNNReal : ℝ) ≤ θ by rw [htcoe]; exact htθ)
    have hcell : ∀ n,
        min ((i n : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ < t.toNNReal ∧
        t.toNNReal ≤ min (((i n + 1 : ℕ) : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ := by
      intro n
      constructor
      · apply NNReal.coe_lt_coe.mp
        rw [htcoe]
        exact (hc n).1
      · apply NNReal.coe_le_coe.mp
        rw [htcoe]
        exact (hc n).2.1
    obtain ⟨hl, hr⟩ := avram_locmoll_band_clipped_selected_tags_limit H θ t.toNNReal htθ' m i hm hcell
    have he' : (t.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
      rw [← ENNReal.ofReal_coe_nnreal, htcoe]
      exact he.resolve_left hz
    obtain ⟨ha,hb,hc'⟩ := avram_locmoll_band_cell_endpoint_limits X x q D hD ω θ t.toNNReal
      (Real.toNNReal_pos.mpr hp) htθ' he' _ _ hl hr
    refine ⟨ha.congr (fun n => (hc n).2.2.1.symm), hb.congr (fun n => (hc n).2.2.2.1.symm), ?_⟩
    rw [htcoe] at hc'
    exact hc'.congr (fun n => (hc n).2.2.2.2.symm)
