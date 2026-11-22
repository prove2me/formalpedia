-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_root_scale_origin_pos_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T09:45:05.326812+00:00
-- url     : https://prove2.me/submissions/284b8d41-0d55-442d-a293-7edfc9efdbd1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_eventual_psi_above_no_standing_public
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_drift_pos_linear_upper_fc6b
import Theorems.Thm_AvramDividend_Classical_p2m81_scale_split_bound
import Theorems.Thm_AvramDividend_Classical_p2m81_tauberian_exp_package
import Theorems.Thm_AvramDividend_Classical_p2m81_cont_pick_small
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    0 < W 0 := by
  obtain ⟨_, hnn, hcont, hmono, hlap⟩ := hW
  obtain ⟨hd, hu⟩ := p2m81_bv_root_drift_pos_linear_upper_fc6b X q φ hq hφ hroot hBV
  obtain ⟨b, hb, hψ⟩ := p2m81_bv_root_eventual_psi_above_no_standing_public X q φ hq hφ hroot hBV
  by_contra! hn
  have hz : W 0 = 0 := le_antisymm hn (hnn 0 le_rfl)
  obtain ⟨a, ha, hWa⟩ := p2m81_cont_pick_small W (1 / X.drift) hcont hz (one_div_pos.mpr hd)
  let K := (X.ψ b - q)⁻¹
  have hEv : ∀ᶠ β : ℝ in atTop, 0 < β ∧ q < X.ψ β := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop b] with β hβ hbβ
    exact ⟨hβ, hψ β hbβ⟩
  have hbound := p2m81_scale_split_bound W X.ψ q a b K ha hnn
    (fun _ _ hx hy hxy => hmono hx hy hxy) hlap hb (hψ b le_rfl)
    (hlap b hb (hψ b le_rfl)).2 hEv
  have hlim := (p2m81_tauberian_exp_package 1 zero_lt_one).2.2 a K b ha
  have hsmall : ∀ᶠ β : ℝ in atTop, β * Real.exp (-(β - b) * a) * K < 1 / X.drift - W a :=
    hlim.eventually (show ∀ᶠ t : ℝ in 𝓝 0, t < 1 / X.drift - W a from
      Iio_mem_nhds (sub_pos.mpr hWa))
  obtain ⟨β, hgood, hbnd, hsm⟩ := (hEv.and (hbound.and hsmall)).exists
  have hlower : 1 / X.drift < β / (X.ψ β - q) := by
    rw [div_lt_div_iff₀ hd (sub_pos.mpr hgood.2)]
    nlinarith [hu β hgood.1.le]
  linarith
