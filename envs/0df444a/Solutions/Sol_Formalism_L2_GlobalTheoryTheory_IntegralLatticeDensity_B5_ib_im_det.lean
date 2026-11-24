-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ib_im_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:53:29.369505+00:00
-- url     : https://prove2.me/submissions/76103ad1-24bc-4dd8-8297-040b47490023

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_IdealBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_ib_im_conj_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution {K : Type} [Field K] [NumberField K] (ψ : 𝓞 K →+* ℂ) (a₀ b₀ : ℂ)
    (B : Module.Basis (Fin 2) ℤ (𝓞 K)) (hB0 : ψ (B 0) = a₀) (hB1 : ψ (B 1) = b₀)
    (v : Fin 2 → 𝓞 K) :
    ((starRingEnd ℂ) (ψ (v 0)) * ψ (v 1)).im = (B.det v : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by
  have hv : ∀ j, ψ (v j) = (B.repr (v j) 0 : ℂ) * a₀ + (B.repr (v j) 1 : ℂ) * b₀ := by
    intro j
    conv_lhs => rw [← B.sum_repr (v j)]
    simp [Fin.sum_univ_two, map_add, hB0, hB1, zsmul_eq_mul]
  rw [Module.Basis.det_apply, Matrix.det_fin_two, hv 0, hv 1]
  simp only [Module.Basis.toMatrix_apply, ib_im_conj_mul]
  push_cast
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im]
  ring
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
