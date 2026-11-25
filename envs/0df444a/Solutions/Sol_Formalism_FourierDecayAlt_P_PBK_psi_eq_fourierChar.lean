-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.psi_eq_fourierChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:58:12.009048+00:00
-- url     : https://prove2.me/submissions/f47e5496-5ae2-4f5c-8484-766f14168a7a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (β w z : ℂ) :
    G.psi β (w * z) = ((Real.fourierChar (-⟪z, freq β w⟫_ℝ) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, G.psi, freq, real_inner_smul_right, Complex.inner]
  congr 1
  have hre : (-conj (β * w) * conj z).re = -(β * (w * z)).re := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  rw [hre]
  push_cast
  field_simp
end Formalism.FourierDecayAlt.P.PBK
