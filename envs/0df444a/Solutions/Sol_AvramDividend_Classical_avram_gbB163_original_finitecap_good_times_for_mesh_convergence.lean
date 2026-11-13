-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB163_original_finitecap_good_times_for_mesh_convergence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:14:43.641202+00:00
-- url     : https://prove2.me/submissions/82cbe453-864c-41ad-8643-865e4ab600bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
import Theorems.Thm_AvramDividend_Classical_avram_gbB100_original_gaussian_fixed_level_occupation_null
import Theorems.Thm_AvramDividend_Classical_avram_gbB164_countable_nonnegative_discontinuities_ae_real_continuity
import Theorems.Thm_AvramDividend_Classical_avram_gbB165_time_level_null_implies_ae_avoids_level
import Theorems.Thm_AvramDividend_Classical_avram_gbB167_original_finitecap_clipped_band_deriv_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
    (j : ℕ) :
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let a : ℝ := δ / 2
    let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
      x + X.X s ω - rightLimit D s ω
    let H : ℝ → Ω → ℝ := fun t ω =>
      if (Real.toNNReal t) < ρ ω then
        Real.exp (-(q * t)) *
          (if Y (Real.toNNReal t) ω ∈ Icc a b then
            deriv w (Y (Real.toNNReal t) ω) else 1)
      else 0
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
          (if Y (s i) ω ∈ Icc a b then deriv w (Y (s i) ω)
            else 1) else 0)
        else 0)
    ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      ContinuousAt (fun s : ℝ => Y (Real.toNNReal s) ω) t ∧
      Y (Real.toNNReal t) ω ≠ a ∧
      Y (Real.toNNReal t) ω ≠ b ∧
      t ≠ (ρ ω : ℝ) ∧
      (Y (Real.toNNReal t) ω ∈ Ioo a b →
        ContinuousAt (deriv w) (Y (Real.toNNReal t) ω)) := by
  intro b a Y H K
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hCount := avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
    X hν D hDiv x
  have hCont : ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      ContinuousAt (fun s : ℝ => Y (Real.toNNReal s) ω) t := by
    filter_upwards [hCount] with ω hc
    simpa only [Y] using
      (avram_gbB164_countable_nonnegative_discontinuities_ae_real_continuity
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) hc n)
  have hOccA := avram_gbB100_original_gaussian_fixed_level_occupation_null
    X hBV hν x a D hDiv n (fun _ => (n : ℝ≥0))
  have hOccB := avram_gbB100_original_gaussian_fixed_level_occupation_null
    X hBV hν x b D hDiv n (fun _ => (n : ℝ≥0))
  have hAEa : ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      Y (Real.toNNReal t) ω ≠ a := by
    filter_upwards [hOccA] with ω hω
    apply avram_gbB165_time_level_null_implies_ae_avoids_level
      n (fun t : ℝ => Y (Real.toNNReal t) ω) a
    convert hω using 1
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Y, NNReal.coe_natCast]
    tauto
  have hAEb : ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      Y (Real.toNNReal t) ω ≠ b := by
    filter_upwards [hOccB] with ω hω
    apply avram_gbB165_time_level_null_implies_ae_avoids_level
      n (fun t : ℝ => Y (Real.toNNReal t) ω) b
    convert hω using 1
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Y, NNReal.coe_natCast]
    tauto
  have hRho (ω : Ω) : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      t ≠ (ρ ω : ℝ) := by
    apply (ae_iff).2
    simp
  have hSmooth (y : ℝ) (hy : y ∈ Ioo a b) :
      ContinuousAt (deriv w) y :=
    avram_gbB167_original_finitecap_clipped_band_deriv_continuous
      w C hC hFiniteCap hw_smooth δ hδ j y hy
  filter_upwards [hCont, hAEa, hAEb] with ω hc ha hb
  filter_upwards [hc, ha, hb, hRho ω] with t ht hta htb htr
  exact ⟨ht, hta, htb, htr, fun hy => hSmooth _ hy⟩
