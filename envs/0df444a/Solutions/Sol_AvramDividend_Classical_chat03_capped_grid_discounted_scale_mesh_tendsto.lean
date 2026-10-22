-- Prove2me | solution 1 for AvramDividend.Classical.chat03_capped_grid_discounted_scale_mesh_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T13:57:19.226874+00:00
-- url     : https://prove2.me/submissions/2ce081c6-f3e3-477e-87e1-f3946a494729

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_discounted_scale_zero_continuity
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Convergence of capped discounted q-scale payoffs along any vanishing mesh
sequence with eventually genuine minimal strict first-grid crossings.
The origin condition W(0)=0 handles possible zero-reserve limits.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (discount : ℝ≥0 → ℝ)
    (hdiscount : Continuous discount)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < first n →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω))) :
    Tendsto (fun n =>
      discount (min ((first n : ℝ≥0) * mesh n) T) *
        W (x + X.X (min ((first n : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (discount (min τ T) * W (x + X.X (min τ T) ω))) := by
  refine Filter.tendsto_def.2 ?_
  intro U hU
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.1 hU
  obtain ⟨δ, hδ, hfine⟩ :=
    chat03_capped_grid_discounted_scale_zero_continuity
      X q W hW hzero ω lower upper x τ T hτ
      discount hdiscount V hVopen hVmem
  have hIio : Set.Iio δ ∈ 𝓝 (0 : ℝ≥0) :=
    isOpen_Iio.mem_nhds hδ
  filter_upwards [hmesh.eventually hIio, hfirst] with n hn hfn
  obtain ⟨k, hk, hkfirst, hpay⟩ := hfine (mesh n) (hpos n) hn
  have hle : first n ≤ k := by
    by_contra h
    exact hfn.2 k (Nat.lt_of_not_ge h) hk
  have hge : k ≤ first n := by
    by_contra h
    exact hkfirst (first n) (Nat.lt_of_not_ge h) hfn.1
  have heq : first n = k := le_antisymm hle hge
  apply hVsub
  simpa only [heq] using hpay
