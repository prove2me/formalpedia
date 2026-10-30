-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_original_nonroot_above_phi_descending_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T06:51:32.085989+00:00
-- url     : https://prove2.me/submissions/8744e2ff-2a31-4723-9443-57f2928f5f31

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam m β : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hβ : φ < β) (hβne : β ≠ φ + lam)
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
  have h1 := avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real X φ q p β hφ.le hq.le
    hroot hp hJoint
  dsimp only at h1
  have h2 := avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap X φ q p lam (-φ) hφ hq hroot hp
    hlam hlamroot (by linarith)
  have h3 := avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta X q φ p lam m hq hφ
    hroot hp hlam hlamroot hm hmderiv hJoint (β - φ) (by linarith)
  have hne : β - φ ≠ lam := by
    intro h; apply hβne; linarith
  rw [if_neg hne] at h3
  have e1 : φ + (β - φ) = β := by ring
  have e2 : p - (X.ψ β - q) = p + q - X.ψ β := by ring
  have e3 : lam - (β - φ) = φ + lam - β := by ring
  rw [e1, e2, e3] at h3
  have e4 : lam - -φ = φ + lam := by ring
  rw [e4] at h2
  rw [h1, ← mul_assoc, ← mul_assoc, mul_comm (ENNReal.ofReal (φ + lam)) (ENNReal.ofReal (p + q)),
    mul_assoc, mul_assoc, ← mul_assoc (ENNReal.ofReal (φ + lam))]
  rw [h2, h3]
