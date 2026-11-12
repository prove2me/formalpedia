-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_aesquare_dominated_limit_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:57:06.394011+00:00
-- url     : https://prove2.me/submissions/a705de39-8127-46fe-913d-fe6281bcd105

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (f : ℕ → Ω → ℝ) (g B : Ω → ℝ)
    (hf : ∀ k, Integrable (f k) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop (𝓝 (g ω)))
    (hB : Integrable (fun ω => (B ω) ^ 2) P)
    (hdom : ∀ᵐ ω ∂P, ∀ k, ‖f k ω‖ ≤ B ω) :
    Integrable (fun ω => (g ω) ^ 2) P := by
  have hgm : AEStronglyMeasurable g P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hf k).aestronglyMeasurable) hlim
  have hle : ∀ᵐ ω ∂P, ‖(g ω) ^ 2‖ ≤ (B ω) ^ 2 := by
    filter_upwards [hlim, hdom] with ω hl hd
    have hc : IsClosed (Set.Iic (B ω)) := isClosed_Iic
    have hnorm : ‖g ω‖ ≤ B ω :=
      hc.mem_of_tendsto hl.norm (Filter.Eventually.of_forall hd)
    have hBpos : 0 ≤ B ω := le_trans (norm_nonneg _) (hd 0)
    calc
      ‖(g ω) ^ 2‖ = ‖g ω‖ ^ 2 := norm_pow (g ω) 2
      _ ≤ (B ω) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hnorm)
          (add_nonneg hBpos (norm_nonneg (g ω)))]
  exact hB.mono' (hgm.pow 2) hle
