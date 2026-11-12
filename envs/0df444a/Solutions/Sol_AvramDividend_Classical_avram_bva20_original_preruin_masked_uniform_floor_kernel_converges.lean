-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_original_preruin_masked_uniform_floor_kernel_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:01:12.029869+00:00
-- url     : https://prove2.me/submissions/da938dc9-0d16-40f5-8274-3cb88ffbbf72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_physical_discounted_mark_uniform_floor_converges
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Strictly pre-ruin floor samples have an active original closed-cap compensator mask. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hpre : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q T : ℝ) (hT : 0 < T) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    let F : ℝ≥0 → ℝ := fun r => Real.exp (-(q * (r : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν
    Tendsto (fun n =>
      if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C then F (s n) else 0)
      atTop (𝓝 (F t)) := by
  intro s U F
  have hfloor := avram_bvb_b21_original_uniform_floor_samples_converge_from_left
    T (t : ℝ) hT (NNReal.coe_nonneg t)
  have hs_le : ∀ n, s n ≤ t := by
    intro n
    exact (Real.toNNReal_le_iff_le_coe).2 (hfloor.1 n)
  have hPlain : Tendsto (fun n => F (s n)) atTop (𝓝 (F t)) := by
    simpa [s, U, F] using
      (avram_bvb_b21_original_physical_discounted_mark_uniform_floor_converges
        X hX hBV x C hxc D hD ω S t ht htpos hpre hsource hFinite
        w hw_cont hw_neg hActivity q T hT)
  have hMask (n : ℕ) : (s n : ℝ≥0∞) < ruinTime X x D ω ∧
      0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C := by
    have hpre_n : (s n : ℝ≥0∞) < ruinTime X x D ω :=
      lt_of_le_of_lt (by exact_mod_cast hs_le n) hpre
    have hcap : 0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C := by
      simpa [U] using avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
        X x C hxc D hD ω (s n) (Or.inr hpre_n)
    exact ⟨hpre_n, hcap⟩
  have hEq :
      (fun n => if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C then F (s n) else 0) =
      (fun n => F (s n)) := by
    funext n
    simp only [if_pos (hMask n)]
  rw [hEq]
  exact hPlain
