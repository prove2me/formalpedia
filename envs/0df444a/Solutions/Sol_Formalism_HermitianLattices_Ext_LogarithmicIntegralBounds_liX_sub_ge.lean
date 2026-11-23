-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.liX_sub_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:13.171824+00:00
-- url     : https://prove2.me/submissions/90a78675-bc4a-403f-ab8e-377814b69f25

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_intervalIntegrable_inv_log

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
theorem _root_.solution {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ liX b - liX a := by
  have hb : 2 ≤ b := le_trans ha hab
  have hsub : liX b - liX a = ∫ t in a..b, 1 / Real.log t := by
    unfold liX
    exact intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log le_rfl hb)
      (intervalIntegrable_inv_log le_rfl ha)
  rw [hsub]
  have hconst : ∫ _t in a..b, (1 / Real.log b) = (b - a) / Real.log b := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab intervalIntegrable_const (intervalIntegrable_inv_log ha hb)
  intro t ht
  have h2t : 2 ≤ t := le_trans ha ht.1
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  exact one_div_le_one_div_of_le hlogt (Real.log_le_log (by linarith) ht.2)
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
