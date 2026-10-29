-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_real_finite_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:16:43.849056+00:00
-- url     : https://prove2.me/submissions/e7ea63b6-5039-4ba1-81eb-b4a32920fb8a

import Mathlib.Probability.Moments.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_levy_positive_root_strict_gap_below
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_laplace_crossmul
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_lintegral_eq_mgf_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The real original-clock descending Wiener–Hopf identity holds on
the full positive finite-rate strip, without assuming its rate gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (β : ℝ) (hβ : 0 < β) (hβlam : β < lam) :
    (mgf (fun z : Ω × ℝ =>
      -(runningSup X (Real.toNNReal z.2) z.1 -
        X.X (Real.toNNReal z.2) z.1))
      (P.prod (expMeasure p)) β) * (p - X.ψ β) =
    (p / lam) * (lam - β) := by
  let D : Ω × ℝ → ℝ := fun z =>
    runningSup X (Real.toNNReal z.2) z.1 -
      X.X (Real.toNNReal z.2) z.1
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure p)
  let L : ℝ := mgf (fun z => -D z) μ β
  have hgap : X.ψ β < p :=
    avram_ws01e_bt_new_levy_positive_root_strict_gap_below
      X p lam β hp hlam hroot hβ.le hβlam
  have hCross : ENNReal.ofReal (p - X.ψ β) * ENNReal.ofReal lam *
      (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z)) ∂μ) =
      ENNReal.ofReal (lam - β) * ENNReal.ofReal p := by
    simpa [D, μ] using
      (avram_ws01e_bt_new_original_clock_descending_laplace_crossmul
        X p hp lam hlam hroot β hβ.le hβlam hgap)
  have hBridge :
      (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z)) ∂μ) =
      ENNReal.ofReal L := by
    simpa [D, μ, L] using
      (avram_ws01e_bt_new_original_clock_descending_lintegral_eq_mgf_positive
        X p hp β hβ)
  rw [hBridge] at hCross
  have hLNonneg : 0 ≤ L := by
    dsimp [L]
    exact mgf_nonneg
  have hReal : (p - X.ψ β) * lam * L = (lam - β) * p := by
    calc
      (p - X.ψ β) * lam * L =
          (ENNReal.ofReal (p - X.ψ β) *
            ENNReal.ofReal lam * ENNReal.ofReal L).toReal := by
            simp only [ENNReal.toReal_mul,
              ENNReal.toReal_ofReal (sub_nonneg.mpr hgap.le),
              ENNReal.toReal_ofReal hlam.le,
              ENNReal.toReal_ofReal hLNonneg]
      _ = (ENNReal.ofReal (lam - β) * ENNReal.ofReal p).toReal :=
        congrArg ENNReal.toReal hCross
      _ = (lam - β) * p := by
        simp only [ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hβlam.le),
          ENNReal.toReal_ofReal hp.le]
  have hDiv : L * (p - X.ψ β) = p * (lam - β) / lam := by
    apply (eq_div_iff (ne_of_gt hlam)).2
    calc
      (L * (p - X.ψ β)) * lam =
          (p - X.ψ β) * lam * L := by ring
      _ = (lam - β) * p := hReal
      _ = p * (lam - β) := by ring
  change L * (p - X.ψ β) = (p / lam) * (lam - β)
  calc
    L * (p - X.ψ β) = p * (lam - β) / lam := hDiv
    _ = (p / lam) * (lam - β) := by ring
