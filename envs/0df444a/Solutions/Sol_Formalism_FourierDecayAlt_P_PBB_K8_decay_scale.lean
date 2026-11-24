-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBB.K8.decay_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:08:37.821219+00:00
-- url     : https://prove2.me/submissions/57606172-f308-4f75-b245-d004a2d80570

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramLocTendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBB Formalism.FourierDecayAlt.P.PBB.K8
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBB.K8
theorem _root_.solution (g : ℝ) (hg : 1 ≤ g) (w : ℂ) :
    ((1 + ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖) ^ 3)⁻¹ ≤ 8 * dw w := by
  have hn : ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖ = g / 2 * ‖w‖ := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (by linarith : (0:ℝ) < g)]
    norm_num
  rw [hn]
  have h0 : 0 < (1 + ‖w‖) / 2 := by positivity
  have h1 : (1 + ‖w‖) / 2 ≤ 1 + g / 2 * ‖w‖ := by nlinarith [norm_nonneg w]
  calc ((1 + g / 2 * ‖w‖) ^ 3)⁻¹ ≤ (((1 + ‖w‖) / 2) ^ 3)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le h1 3)
    _ = 8 * dw w := by unfold dw; field_simp; ring
end Formalism.FourierDecayAlt.P.PBB.K8
