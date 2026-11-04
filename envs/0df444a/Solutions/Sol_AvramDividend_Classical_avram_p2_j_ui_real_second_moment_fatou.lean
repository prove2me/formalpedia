-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_real_second_moment_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:36:08.476128+00:00
-- url     : https://prove2.me/submissions/7e5b8917-904f-48b7-894f-1b0e207029ba

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal

/-! Fatou inheritance of real second moments for genuine almost-everywhere limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ n, Measurable (Y n))
    (hz : AEStronglyMeasurable Z P)
    (hInt : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) P)
    (hB : ∀ n, (∫ ω, (Y n ω) ^ 2 ∂P) ≤ C)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable (fun ω => (Z ω) ^ 2) P ∧
      (∫ ω, (Z ω) ^ 2 ∂P) ≤ C := by
  let F : ℕ → Ω → ENNReal := fun n ω => ENNReal.ofReal ((Y n ω) ^ 2)
  have hFm : ∀ n, Measurable (F n) :=
    fun n => ((hm n).pow_const 2).ennreal_ofReal
  have hFi : ∀ n, (∫⁻ ω, F n ω ∂P) =
      ENNReal.ofReal (∫ ω, (Y n ω) ^ 2 ∂P) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal
      (hInt n) (Eventually.of_forall fun ω => by positivity)).symm
  have hlim : ∀ᵐ ω ∂P,
      ENNReal.ofReal ((Z ω) ^ 2) =
        Filter.liminf (fun n => F n ω) atTop := by
    filter_upwards [hae] with ω hω
    have ht : Tendsto (fun n => F n ω) atTop
        (nhds (ENNReal.ofReal ((Z ω) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hω.pow 2)
    exact ht.liminf_eq.symm
  have hFatou : (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≤
      Filter.liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop := by
    rw [lintegral_congr_ae hlim]
    exact lintegral_liminf_le hFm
  have hupper : Filter.liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop ≤
      ENNReal.ofReal C := by
    refine (Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_)).trans
      (by rw [liminf_const])
    rw [hFi n]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have hbound := hFatou.trans hupper
  have hzm : AEStronglyMeasurable (fun ω => (Z ω) ^ 2) P := hz.pow 2
  have he : ∀ ω, ‖(Z ω) ^ 2‖ₑ =
      ENNReal.ofReal ((Z ω) ^ 2) := fun ω =>
    Real.enorm_of_nonneg (by positivity)
  refine ⟨⟨hzm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_enorm]
    simp_rw [he]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun ω => by positivity) hzm]
    calc
      (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P).toReal
          ≤ (ENNReal.ofReal C).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      _ = C := ENNReal.toReal_ofReal hC
