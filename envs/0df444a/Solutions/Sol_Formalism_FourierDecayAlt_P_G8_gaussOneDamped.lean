-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.gaussOneDamped
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:13.078803+00:00
-- url     : https://prove2.me/submissions/9d77afce-52e5-4553-8da4-5b7d8b1ac491

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_integral_gK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution : GaussOneDamped := by
  intro β a δ hδ
  obtain ⟨γ, hγ⟩ : ∃ γ : ℂ, γ = β * a / 2 := ⟨_, rfl⟩
  have hint : ∀ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (a * w ^ 2 / 2) =
      gK δ γ.re γ.im (Complex.measurableEquivRealProd w) := by
    intro w
    have h1 : (β * (a * w ^ 2 / 2)).re =
        γ.re * (w.re ^ 2 - w.im ^ 2) - γ.im * (2 * w.re * w.im) := by
      have : β * (a * w ^ 2 / 2) = γ * (w * w) := by rw [hγ]; ring
      rw [this]; simp only [Complex.mul_re, Complex.mul_im]; ring
    rw [psi, gK, Complex.ofReal_exp, ← Complex.exp_add, h1, Complex.sq_norm, Complex.normSq_apply,
      Complex.measurableEquivRealProd_apply]
    congr 1
    push_cast
    ring
  have hn : γ.re ^ 2 + γ.im ^ 2 = ‖β‖ ^ 2 * ‖a‖ ^ 2 / 4 := by
    have : ‖γ‖ ^ 2 = γ.re ^ 2 + γ.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← this, hγ, norm_div, norm_mul]; simp; ring
  simp_rw [hint]
  rw [mu, integral_smul_nnreal_measure,
    Complex.volume_preserving_equiv_real_prod.integral_comp
      (MeasurableEquiv.measurableEmbedding _) (gK δ γ.re γ.im), integral_gK δ _ _ hδ,
    NNReal.smul_def, Real.coe_toNNReal _ (by positivity), Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  have hR : 0 < δ ^ 2 + γ.re ^ 2 + γ.im ^ 2 := by positivity
  have e : 4 * δ ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2 = 2 ^ 2 * (δ ^ 2 + γ.re ^ 2 + γ.im ^ 2) := by
    linear_combination (-4 : ℝ) * hn
  rw [e, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hs : 0 < Real.sqrt (δ ^ 2 + γ.re ^ 2 + γ.im ^ 2) := Real.sqrt_pos.2 hR
  have := Real.pi_pos
  field_simp
end Formalism.FourierDecayAlt.P.G8
