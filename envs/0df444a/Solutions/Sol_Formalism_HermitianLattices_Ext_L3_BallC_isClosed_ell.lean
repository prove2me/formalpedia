-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallC.isClosed_ell
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:45.811832+00:00
-- url     : https://prove2.me/submissions/f9d3aa7e-b7c3-4c86-abc6-e9d71b0d1ee5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VolumeNormSqLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallC
variable {M : ℕ} (a : Fin M → ℝ)
namespace Formalism.HermitianLattices.Ext.L3.BallC
theorem _root_.solution : IsClosed (ell a) := by
  unfold ell
  exact isClosed_le (continuous_finset_sum _ fun i _ =>
    continuous_const.mul (Complex.continuous_normSq.comp (continuous_apply i))) continuous_const
end Formalism.HermitianLattices.Ext.L3.BallC
