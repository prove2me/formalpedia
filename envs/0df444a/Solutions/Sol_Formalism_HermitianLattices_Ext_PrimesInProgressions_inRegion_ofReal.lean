-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.inRegion_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:56:45.43854+00:00
-- url     : https://prove2.me/submissions/1501eb2f-ccb6-4458-9fd1-f8ef3d5e76d6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (c : ℝ) (q : ℕ) (β : ℝ) :
    InRegion c q (β : ℂ) ↔ 1 - c / Real.log ((q : ℝ) * 2) ≤ β := by
  unfold InRegion
  rw [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
