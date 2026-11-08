-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps16_original_signed_integral_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:39:21.692507+00:00
-- url     : https://prove2.me/submissions/36f962b5-7328-4447-86da-e454bb06d593

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_shifted_real_integral_upperlim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Remove the common integrable dominating envelope from the accepted
shifted real-integral inequality, obtaining signed reverse Fatou for the
actual Lévy measure, without requiring finite jump intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ → ℝ) (hhmeas : Measurable h)
    (hh_nonneg : ∀ z : ℝ, 0 ≤ h z)
    (hhfinite : (∫⁻ z, ENNReal.ofReal (2 * h z) ∂X.ν) ≠ ⊤)
    (hint : Integrable h X.ν)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hfmeas : ∀ n, Measurable (f n)) (hgmeas : Measurable g)
    (habs : ∀ n z, |f n z| ≤ h z)
    (hgabs : ∀ z, |g z| ≤ h z)
    (hfint : ∀ n, Integrable (f n) X.ν)
    (hgint : Integrable g X.ν)
    (hpoint : ∀ᵐ z ∂X.ν,
      Filter.limsup (fun n : ℕ => ENNReal.ofReal (h z + f n z)) atTop ≤
        ENNReal.ofReal (h z + g z)) :
    Filter.limsup (fun n : ℕ => ∫ z, f n z ∂X.ν) atTop ≤
      ∫ z, g z ∂X.ν := by
  let F : ℕ → ℝ := fun n => ∫ z, f n z ∂X.ν
  have hup (n : ℕ) : F n ≤ ∫ z, h z ∂X.ν := by
    apply integral_mono (hfint n) hint
    intro z
    exact (abs_le.mp (habs n z)).2
  have hlo (n : ℕ) : -(∫ z, h z ∂X.ν) ≤ F n := by
    have hb := integral_mono hint.neg (hfint n)
      (show (fun z : ℝ => -h z) ≤ f n from fun z =>
        (abs_le.mp (habs n z)).1)
    simpa only [Pi.neg_apply, integral_neg, F] using hb
  have hFupper : Filter.IsBoundedUnder (· ≤ ·) atTop F := by
    apply Filter.isBoundedUnder_iff_eventually_bddAbove.mpr
    refine ⟨Set.univ, ?_, Filter.Eventually.of_forall (by simp)⟩
    refine ⟨∫ z, h z ∂X.ν, ?_⟩
    rintro a ⟨n, -, rfl⟩
    exact hup n
  have hFlower : Filter.IsCoboundedUnder (· ≤ ·) atTop F := by
    apply Filter.isCoboundedUnder_le_of_eventually_le atTop
    exact Filter.Eventually.of_forall hlo
  have hplus := avram_ubv_ito_jumps16_original_shifted_real_integral_upperlim
    X h hhmeas hh_nonneg hhfinite f g hfmeas hgmeas habs hgabs hpoint
  have hadd (n : ℕ) :
      (∫ z, h z + f n z ∂X.ν) =
        (∫ z, h z ∂X.ν) + F n :=
    integral_add hint (hfint n)
  have hlim : (∫ z, h z ∂X.ν) + Filter.limsup F atTop ≤
      (∫ z, h z ∂X.ν) + ∫ z, g z ∂X.ν := by
    calc
      (∫ z, h z ∂X.ν) + Filter.limsup F atTop =
          Filter.limsup (fun n : ℕ => (∫ z, h z ∂X.ν) + F n) atTop :=
        (limsup_const_add atTop F (∫ z, h z ∂X.ν) hFupper hFlower).symm
      _ = Filter.limsup (fun n : ℕ => ∫ z, h z + f n z ∂X.ν) atTop := by
        congr 1
        funext n
        exact (hadd n).symm
      _ ≤ ∫ z, h z + g z ∂X.ν := hplus
      _ = (∫ z, h z ∂X.ν) + ∫ z, g z ∂X.ν := integral_add hint hgint
  exact (add_le_add_iff_left (∫ z, h z ∂X.ν)).mp hlim
