-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhl_geom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:31:30.853565+00:00
-- url     : https://prove2.me/submissions/edf72c9d-9d14-4563-ae61-c8d6d5aacd33

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocalA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocalB

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
theorem _root_.solution (t : ℝ) (z : ℂ) (hz : ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25) :
    1 / 2 ≤ z.re ∧ 1 + ‖z‖ ≤ 2 * (|t| + 2) := by
  have hre : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
    simp
  have h1 := abs_re_le_norm (z - ((26 / 25 : ℂ) + t * I))
  rw [sub_re, hre] at h1
  have hn : ‖((26 / 25 : ℂ) + t * I)‖ ≤ 26 / 25 + |t| := by
    calc ‖((26 / 25 : ℂ) + t * I)‖ ≤ ‖(26 / 25 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 26 / 25 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  refine ⟨?_, ?_⟩
  · have := (abs_le.mp (h1.trans hz)).1; linarith
  · have := norm_sub_norm_le z ((26 / 25 : ℂ) + t * I)
    linarith [abs_nonneg t]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
