-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_original_root_descending_scaled
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:27:50.367148+00:00
-- url     : https://prove2.me/submissions/9d7f8f4c-fc97-4d8e-803d-4c0759b038f9

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The original-clock descending transform at the removable positive
root, with the genuine Lévy exponent derivative and finite scalars. -/
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
    ENNReal.ofReal (φ + lam) *
      (ENNReal.ofReal p *
        (∫⁻ z : Ω × ℝ,
          ENNReal.ofReal (Real.exp
            (-(φ + lam) *
              (runningSup X (Real.toNNReal z.2) z.1 -
                X.X (Real.toNNReal z.2) z.1)))
          ∂(P.prod (expMeasure (p + q))))) =
    ENNReal.ofReal (p + q) *
      (ENNReal.ofReal lam * ENNReal.ofReal (p / (lam * m))) := by
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
  have hDesc :
      (∫⁻ z, ENNReal.ofReal (Real.exp (-lam * D z)) ∂Qp) =
        ENNReal.ofReal (p / (lam * m)) := by
    have h := avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
      X q φ p lam m hq hφ hroot hp hlam hlamroot
      hm hmderiv hJoint lam hlam
    simpa [Qp, S, D] using h
  have hInv :
      ENNReal.ofReal p *
        (∫⁻ z, ENNReal.ofReal (Real.exp (-(φ + lam) * D z))
          ∂(P.prod (expMeasure (p + q)))) =
      ENNReal.ofReal (p + q) *
        ((∫⁻ z, ENNReal.ofReal (Real.exp (-φ * S z)) ∂Qp) *
         (∫⁻ z, ENNReal.ofReal (Real.exp (-lam * D z)) ∂Qp)) := by
    have h := avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
      X φ q p (φ + lam) hφ.le hq.le hroot hp hJoint
    have hShift : φ + lam - φ = lam := by ring
    simpa only [Qp, S, D, hShift] using h
  change ENNReal.ofReal (φ + lam) *
    (ENNReal.ofReal p *
      (∫⁻ z, ENNReal.ofReal (Real.exp (-(φ + lam) * D z))
        ∂(P.prod (expMeasure (p + q))))) = _
  calc
    _ = ENNReal.ofReal (φ + lam) *
        (ENNReal.ofReal (p + q) *
          ((∫⁻ z, ENNReal.ofReal (Real.exp (-φ * S z)) ∂Qp) *
           (∫⁻ z, ENNReal.ofReal (Real.exp (-lam * D z)) ∂Qp))) := by
            rw [hInv]
    _ = ENNReal.ofReal (p + q) *
        ((ENNReal.ofReal (φ + lam) *
            (∫⁻ z, ENNReal.ofReal (Real.exp (-φ * S z)) ∂Qp)) *
          (∫⁻ z, ENNReal.ofReal (Real.exp (-lam * D z)) ∂Qp)) := by ac_rfl
    _ = _ := by rw [hSup, hDesc]
