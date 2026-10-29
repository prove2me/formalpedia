-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_all_beta_from_genuine_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:44:10.250126+00:00
-- url     : https://prove2.me/submissions/65ffbc3b-7015-4bf2-ab96-3bfe2f91d5c0

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_all_beta_wh_analytic_continuation_with_removable_root
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_clock_descending_mgf_analytic_positive
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_shifted_levy_psi_analytic_on_positive
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
import Theorems.Thm_AvramDividend_Classical_esscher_levy_shift_strictMonoOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam m : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
    (hStrip : ∀ β : ℝ, 0 < β → β < lam →
      mgf
        (fun z : Ω × ℝ =>
          -(runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1))
        ((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) β *
      (p - (X.ψ (φ + β) - q)) = (p / lam) * (lam - β)) :
    ∀ β : ℝ, 0 < β →
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp
          (-β * (runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1)))
        ∂((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) =
      ENNReal.ofReal
        (if β = lam then p / (lam * m)
         else (p / lam) * ((lam - β) / (p - (X.ψ (φ + β) - q)))) := by
  let μ : Measure (Ω × ℝ) :=
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
  let Y : Ω × ℝ → ℝ := fun z =>
    -(runningSup X (Real.toNNReal z.2) z.1 -
      X.X (Real.toNNReal z.2) z.1)
  let L : ℝ → ℝ := mgf Y μ
  let g : ℝ → ℝ := fun β => X.ψ (φ + β) - q
  have hLAnalytic : AnalyticOnNhd ℝ L (Ioi (0 : ℝ)) := by
    simpa only [L, Y, μ] using
      (avram_ws01e_b_genuine_tilted_clock_descending_mgf_analytic_positive
        X φ p hφ.le hp hJoint)
  have hgAnalytic : AnalyticOnNhd ℝ g (Ioi (0 : ℝ)) := by
    simpa only [g] using
      (avram_ws01e_b_shifted_levy_psi_analytic_on_positive X φ q hφ)
  have hgRoot : g lam = p := hlamroot
  have hShift : HasDerivAt (fun β : ℝ => φ + β) 1 lam := by
    simpa only [id_eq] using
      (HasDerivAt.const_add φ (hasDerivAt_id lam))
  have hgDeriv : HasDerivAt g m lam := by
    simpa only [g, Function.comp_def, mul_one] using
      (hmderiv.comp lam hShift).sub_const q
  have hgUnique : ∀ β : ℝ, 0 < β → β ≠ lam → g β ≠ p := by
    intro β hβ hne heq
    have hmono := esscher_levy_shift_strictMonoOn X q φ hq hφ hroot
    have hb : β ∈ Ici (0 : ℝ) := hβ.le
    have hl : lam ∈ Ici (0 : ℝ) := hlam.le
    have heq' :
        X.ψ (φ + β) - q = X.ψ (φ + lam) - q := by
      rw [hlamroot]
      exact heq
    exact hne (hmono.injOn hb hl heq')
  have hStrip' : ∀ β : ℝ, 0 < β → β < lam →
      L β * (p - g β) = (p / lam) * (lam - β) := by
    intro β hβ hβlam
    simpa only [L, Y, μ, g] using hStrip β hβ hβlam
  have hAll :=
    avram_ws01e_b_all_beta_wh_analytic_continuation_with_removable_root
      p lam m hp hlam hm L g hLAnalytic hgAnalytic
      hgRoot hgDeriv hgUnique hStrip'
  intro β hβ
  rw [avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
    X φ p hφ.le hp hJoint β hβ]
  exact congrArg ENNReal.ofReal (by simpa only [L, Y, μ, g] using hAll β hβ)
