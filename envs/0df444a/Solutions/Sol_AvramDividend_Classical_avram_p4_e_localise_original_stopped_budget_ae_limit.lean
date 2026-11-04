-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_stopped_budget_ae_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:11.568363+00:00
-- url     : https://prove2.me/submissions/1eac8327-bebf-4547-bc02-e392b8e5d938

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open AvramDividend.Classical

/-- Pass localised signs and exact stopped-budget inequalities to a common a.s. limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (x : ℝ)
    (Tk Ck Mk Gk Hk : ℕ → Ω → ℝ)
    (Term Cash M G H : Ω → ℝ)
    (hBudget : ∀ k, ∀ᵐ ω ∂P,
      Tk k ω + Ck k ω ≤ w x + Mk k ω + Gk k ω + Hk k ω)
    (hSign : ∀ k, ∀ᵐ ω ∂P, Gk k ω + Hk k ω ≤ 0)
    (hT : ∀ᵐ ω ∂P, Tendsto (fun k => Tk k ω) atTop (𝓝 (Term ω)))
    (hC : ∀ᵐ ω ∂P, Tendsto (fun k => Ck k ω) atTop (𝓝 (Cash ω)))
    (hM : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω)))
    (hG : ∀ᵐ ω ∂P, Tendsto (fun k => Gk k ω) atTop (𝓝 (G ω)))
    (hH : ∀ᵐ ω ∂P, Tendsto (fun k => Hk k ω) atTop (𝓝 (H ω))) :
    (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
    (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  have hBudAll : ∀ᵐ ω ∂P, ∀ k,
      Tk k ω + Ck k ω ≤ w x + Mk k ω + Gk k ω + Hk k ω :=
    ae_all_iff.mpr hBudget
  have hSignAll : ∀ᵐ ω ∂P, ∀ k, Gk k ω + Hk k ω ≤ 0 :=
    ae_all_iff.mpr hSign
  constructor
  · filter_upwards [hSignAll, hG, hH] with ω hSignω hGω hHω
    have hsum := hGω.add hHω
    exact le_of_tendsto hsum (Filter.Eventually.of_forall hSignω)
  · filter_upwards [hBudAll, hT, hC, hM, hG, hH] with
      ω hBudω hTω hCω hMω hGω hHω
    have hl := hTω.add hCω
    have hconst : Tendsto (fun _ : ℕ => w x) atTop (𝓝 (w x)) :=
      tendsto_const_nhds
    have hr := ((hconst.add hMω).add hGω).add hHω
    exact le_of_tendsto_of_tendsto hl hr
      (Filter.Eventually.of_forall hBudω)
