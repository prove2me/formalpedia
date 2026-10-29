-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:14:51.11542+00:00
-- url     : https://prove2.me/submissions/51910f43-12ca-4143-a471-42a8ddbb71db

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_genuine_strip_from_indep
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_all_beta_from_genuine_strip

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
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
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
  haveI : IsProbabilityMeasure P := X.isProbability
  have hIndep :=
    avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
      X φ p hφ.le hp hJoint
  have hStrip :=
    avram_ws01e_bf_new_genuine_strip_from_indep
      X q φ p lam hq hφ hroot hp hlam hlamroot hJoint hIndep
  exact avram_ws01e_bf_new_all_beta_from_genuine_strip
    X q φ p lam m hq hφ hroot hp hlam hlamroot
    hm hmderiv hJoint hStrip
