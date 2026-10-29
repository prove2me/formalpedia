-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_original_above_root_descending_scaled
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:15:13.231465+00:00
-- url     : https://prove2.me/submissions/0966186f-013b-4b72-8dc2-37b6a436c818

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The original-clock descending factor above the positive root, in a
positive finite-rate-scaled form that avoids extended-real division. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam m β : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hβ : φ + lam < β)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    ENNReal.ofReal (φ + lam) *
      (ENNReal.ofReal p *
        (∫⁻ z : Ω × ℝ,
          ENNReal.ofReal (Real.exp
            (-β * (runningSup X (Real.toNNReal z.2) z.1 -
              X.X (Real.toNNReal z.2) z.1)))
          ∂(P.prod (expMeasure (p + q))))) =
    ENNReal.ofReal (p + q) *
      (ENNReal.ofReal lam *
        ENNReal.ofReal
          ((p / lam) *
            ((φ + lam - β) / (p + q - X.ψ β)))) := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let Qp : Measure (Ω × ℝ) :=
    (P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ)))
  let S : Ω × ℝ → ℝ := fun z =>
    runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ := fun z =>
    S z - X.X (Real.toNNReal z.2) z.1
  have hSup :
      ENNReal.ofReal (φ + lam) *
        (∫⁻ z, ENNReal.ofReal (Real.exp (-φ * S z)) ∂Qp) =
      ENNReal.ofReal lam := by
    have h := avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
      X φ q p lam (-φ) hφ hq hroot hp hlam hlamroot (by linarith)
    have hShift : lam - (-φ) = φ + lam := by ring
    rw [hShift] at h
    simpa only [Qp, S] using h
  have hδpos : 0 < β - φ := by linarith
  have hδne : β - φ ≠ lam := by linarith
  have hNum : lam - (β - φ) = φ + lam - β := by ring
  have hDen :
      p - (X.ψ (φ + (β - φ)) - q) = p + q - X.ψ β := by
    have hAdd : φ + (β - φ) = β := by ring
    rw [hAdd]
    ring
  have hDesc :
      (∫⁻ z, ENNReal.ofReal (Real.exp (-(β - φ) * D z)) ∂Qp) =
        ENNReal.ofReal
          ((p / lam) * ((φ + lam - β) / (p + q - X.ψ β))) := by
    have h := avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
      X q φ p lam m hq hφ hroot hp hlam hlamroot
      hm hmderiv hJoint (β - φ) hδpos
    simpa only [Qp, S, D, if_neg hδne, hNum, hDen] using h
  have hInv :
      ENNReal.ofReal p *
        (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
          ∂(P.prod (expMeasure (p + q)))) =
      ENNReal.ofReal (p + q) *
        ((∫⁻ z, ENNReal.ofReal (Real.exp (-φ * S z)) ∂Qp) *
         (∫⁻ z, ENNReal.ofReal (Real.exp (-(β - φ) * D z)) ∂Qp)) := by
    simpa only [Qp, S, D] using
      (avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
        X φ q p β hφ.le hq.le hroot hp hJoint)
  change ENNReal.ofReal (φ + lam) *
    (ENNReal.ofReal p *
      (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
        ∂(P.prod (expMeasure (p + q))))) = _
  calc
    _ = ENNReal.ofReal (φ + lam) *
        (ENNReal.ofReal (p + q) *
          ((∫⁻ z, ENNReal.ofReal (Real.exp (-φ * S z)) ∂Qp) *
           (∫⁻ z, ENNReal.ofReal
             (Real.exp (-(β - φ) * D z)) ∂Qp))) := by rw [hInv]
    _ = ENNReal.ofReal (p + q) *
        ((ENNReal.ofReal (φ + lam) *
            (∫⁻ z, ENNReal.ofReal (Real.exp (-φ * S z)) ∂Qp)) *
          (∫⁻ z, ENNReal.ofReal
            (Real.exp (-(β - φ) * D z)) ∂Qp)) := by ac_rfl
    _ = _ := by rw [hSup, hDesc]
