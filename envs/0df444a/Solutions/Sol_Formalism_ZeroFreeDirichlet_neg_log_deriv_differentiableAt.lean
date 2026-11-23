-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.neg_log_deriv_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:20.792776+00:00
-- url     : https://prove2.me/submissions/6ba1ce81-f3ed-4982-9927-1cbdc554cbcc

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RectShiftChi

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
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {w : ℂ}
    (hL : DirichletCharacter.LFunction χ w ≠ 0) : DifferentiableAt ℂ (negLD χ) w := by
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hd' : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) w :=
    ((hLd.analyticAt w).deriv).differentiableAt
  show DifferentiableAt ℂ (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
    DirichletCharacter.LFunction χ s)) w
  exact (hd'.div (hLd w) hL).neg
end Formalism.ZeroFreeDirichlet
