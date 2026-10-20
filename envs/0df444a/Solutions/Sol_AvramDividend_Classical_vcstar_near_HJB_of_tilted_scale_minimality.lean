-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_near_HJB_of_tilted_scale_minimality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T14:23:12.180026+00:00
-- url     : https://prove2.me/submissions/489d7338-eb6a-4cff-9c85-6a5f3a1e7a8e

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_positive_tilted_regular_minimal
import Theorems.Thm_AvramDividend_Classical_vcstar_continuousOn_Icc_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_affine_majorant_at_threshold
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpositive : ∀ x : ℝ, 0 < x → 0 < W x)
    (φ : ℝ) (hφ : 0 < φ)
    (htilt : MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x))
    (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := le_of_lt hpos
  have hcont : ContinuousOn (vcstar W) (Icc 0 a) :=
    vcstar_continuousOn_Icc_below_positive_cstar X q W hW hpos
  have hd :
      ∀ z : ℝ, 0 < z →
        DifferentiableAt ℝ (vcstar W) z ∧
          1 ≤ deriv (vcstar W) z :=
    vcstar_deriv_ge_one_of_positive_tilted_regular_minimal
      W hreg hpositive φ hφ htilt hmin
  have hdiffOn : DifferentiableOn ℝ (vcstar W)
      (interior (Icc 0 a)) := by
    rw [interior_Icc]
    intro t ht
    exact (hd t ht.1).1.differentiableWithinAt
  have hderOn : ∀ t ∈ interior (Icc (0 : ℝ) a),
      (1 : ℝ) ≤ deriv (vcstar W) t := by
    intro t ht
    have hti : t ∈ Ioo (0 : ℝ) a := by
      simpa only [interior_Icc] using ht
    exact (hd t hti.1).2
  have hchord : ∀ z : ℝ, 0 ≤ z → z ≤ a →
      vcstar W z ≤ z - a + vcstar W a := by
    intro z hz0 hza
    have hz : z ∈ Icc (0 : ℝ) a := ⟨hz0, hza⟩
    have haa : a ∈ Icc (0 : ℝ) a := ⟨ha, le_rfl⟩
    have hcore : (1 : ℝ) * (a - z) ≤ vcstar W a - vcstar W z :=
      (convex_Icc (0 : ℝ) a).mul_sub_le_image_sub_of_le_deriv
        hcont hdiffOn hderOn z hz a haa hza
    linarith
  exact vcstar_near_HJB_of_affine_majorant_at_threshold
    X q hq W hW hpos hchord x hx hx1 hthreshold
