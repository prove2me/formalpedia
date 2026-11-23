-- Prove2me | solution 1 for FiniteEnergyPlane.pos_of_hasDerivAt_dlambdaEnergy_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T21:39:56.085016+00:00
-- url     : https://prove2.me/submissions/a549d7a0-0b8d-4a4c-9757-f7de3ef1706a

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_continuous_dlambdaDensity
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_univ_eq_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_ne_top_of_univ_eq_ofReal



/-! Positive growth rate of the `dλ`-energy of a fast plane on discs. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem pos_of_hasDerivAt_dlambdaEnergy_ball_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (ζ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (d : ℝ)
    (hd : HasDerivAt (fun s => (dlambdaEnergy H (ball ζ s) u).toReal) d ρ) : 0 < d := by
  have hfe := hu.1
  set f := dlambdaDensity H u with hf_def
  have hfc : Continuous f := continuous_dlambdaDensity H hH J u hfe
  have hpos : ∀ z, 0 < f z := fun z =>
    (piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ Set.univ isOpen_univ u
      (fun z _ => hfe.2.1 z trivial) hfe.2.2.1 (Set.mem_univ z)).1
      (piDs_ne_zero_of_isFastPlane H hH J hJ u hu z)
  obtain ⟨P, -, hP⟩ := hu.2.1
  have htot := dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ u hfe P hP
  have hfin := fun s => dlambdaEnergy_ne_top_of_univ_eq_ofReal H u P.T htot s
  obtain ⟨w, -, hw⟩ := (isCompact_closedBall ζ (ρ + 1)).exists_isMinOn
    ⟨ζ, mem_closedBall_self (by linarith)⟩ hfc.continuousOn
  set m := f w with hm
  have hm0 : 0 < m := hpos w
  have hstep : ∀ h : ℝ, 0 < h → h < 1 →
      m * (π * ((ρ + h) ^ 2 - ρ ^ 2)) ≤ (dlambdaEnergy H (ball ζ (ρ + h)) u).toReal -
        (dlambdaEnergy H (ball ζ ρ) u).toReal := by
    intro h h0 h1
    have hsub : ball ζ ρ ⊆ ball ζ (ρ + h) := ball_subset_ball (by linarith)
    have hsplit : dlambdaEnergy H (ball ζ (ρ + h)) u = dlambdaEnergy H (ball ζ ρ) u +
        dlambdaEnergy H (ball ζ (ρ + h) \ ball ζ ρ) u := by
      unfold dlambdaEnergy
      rw [← lintegral_union (measurableSet_ball.diff measurableSet_ball) Set.disjoint_sdiff_right,
        Set.union_diff_cancel hsub]
    have hvol : (volume (ball ζ (ρ + h) \ ball ζ ρ)) =
        ENNReal.ofReal (π * ((ρ + h) ^ 2 - ρ ^ 2)) := by
      rw [measure_diff hsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne,
        Complex.volume_ball, Complex.volume_ball]
      have e : ∀ r : ℝ, 0 ≤ r → ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞) =
          ENNReal.ofReal (r ^ 2 * π) := by
        intro r hr
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr]
        congr 1
        rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
      rw [e _ (by linarith), e _ hρ.le, ← ENNReal.ofReal_sub _ (by positivity)]
      congr 1; ring
    have hlow : ENNReal.ofReal (m * (π * ((ρ + h) ^ 2 - ρ ^ 2))) ≤
        dlambdaEnergy H (ball ζ (ρ + h) \ ball ζ ρ) u := by
      rw [ENNReal.ofReal_mul hm0.le, ← hvol, ← setLIntegral_const]
      refine setLIntegral_mono (ENNReal.measurable_ofReal.comp hfc.measurable) fun z hz => ?_
      refine ENNReal.ofReal_le_ofReal (hw ?_)
      have := hz.1
      rw [mem_ball] at this
      rw [mem_closedBall]; linarith
    have hfd : dlambdaEnergy H (ball ζ (ρ + h) \ ball ζ ρ) u ≠ ⊤ :=
      ne_top_of_le_ne_top (hfin (ball ζ (ρ + h))) (lintegral_mono_set Set.diff_subset)
    rw [hsplit, ENNReal.toReal_add (hfin _) hfd, add_sub_cancel_left]
    exact (ENNReal.ofReal_le_iff_le_toReal hfd).1 hlow
  have hslope : Tendsto (slope (fun s => (dlambdaEnergy H (ball ζ s) u).toReal) ρ) (𝓝[>] ρ)
      (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
      (nhdsWithin_mono _ fun x hx => (ne_of_gt hx))
  have hge : m * (π * (2 * ρ)) ≤ d := by
    refine ge_of_tendsto hslope ?_
    filter_upwards [Ioo_mem_nhdsGT (show ρ < ρ + 1 by linarith)] with s hs
    have h := hstep (s - ρ) (by linarith [hs.1]) (by linarith [hs.2])
    rw [add_sub_cancel] at h
    rw [slope_def_field, le_div_iff₀ (by linarith [hs.1])]
    refine le_trans ?_ h
    have h2 : m * (π * (s ^ 2 - ρ ^ 2)) =
        m * (π * (2 * ρ)) * (s - ρ) + m * π * (s - ρ) ^ 2 := by ring
    rw [h2]
    have : 0 ≤ m * π * (s - ρ) ^ 2 := by positivity
    linarith
  exact lt_of_lt_of_le (by positivity) hge

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (ζ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (d : ℝ)
    (hd : HasDerivAt (fun s => (dlambdaEnergy H (ball ζ s) u).toReal) d ρ) : 0 < d :=
  pos_of_hasDerivAt_dlambdaEnergy_ball_aux H hH J hJ u hu ζ ρ hρ d hd
