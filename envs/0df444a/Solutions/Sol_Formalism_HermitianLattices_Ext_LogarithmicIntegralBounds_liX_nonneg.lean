-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.liX_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:29.263996+00:00
-- url     : https://prove2.me/submissions/923f2700-c3a9-4c43-8c17-fec5495515b5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_sub_ge
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {a : ℝ} (ha : 2 ≤ a) : 0 ≤ liX a := by
  have h := liX_sub_ge (le_refl (2:ℝ)) ha
  rw [liX_two, sub_zero] at h
  exact le_trans (div_nonneg (by linarith) (Real.log_nonneg (by linarith))) h
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
