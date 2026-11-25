-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_freq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:58:18.529905+00:00
-- url     : https://prove2.me/submissions/2241808e-8944-4da0-a797-604f2dafb854

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
theorem _root_.solution (β : ℂ) (hβ : β ≠ 0) : Tendsto (freq β) (cocompact ℂ) (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded, Metric.cobounded_eq_cocompact]
  have hn : ∀ w, ‖freq β w‖ = ((2 * Real.pi)⁻¹ * ‖β‖) * ‖w‖ := by
    intro w
    rw [freq, norm_smul, norm_neg, Complex.norm_conj, norm_mul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  simp_rw [hn]
  exact (tendsto_norm_cocompact_atTop).const_mul_atTop (by positivity)
end Formalism.FourierDecayAlt.P.PBK
