-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_integrand_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:18.909313+00:00
-- url     : https://prove2.me/submissions/d162101a-bfac-4962-ad10-1f9e26c506c2

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RectShiftChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_neg_log_deriv_differentiableAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ}
    (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) (hL : DirichletCharacter.LFunction χ w ≠ 0) :
    DifferentiableAt ℂ (Fchi χ y) w := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  show DifferentiableAt ℂ (fun w => negLD χ w * (y : ℂ) ^ w / (w * (w - 1))) w
  refine ((neg_log_deriv_differentiableAt hχ hL).mul ?_).div (by fun_prop) (mul_ne_zero h0 (sub_ne_zero.2 h1))
  exact DifferentiableAt.const_cpow (f := fun w => w) differentiableAt_id (Or.inl hy')
end Formalism.ZeroFreeDirichlet
