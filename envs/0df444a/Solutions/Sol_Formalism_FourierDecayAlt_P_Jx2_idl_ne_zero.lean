-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.idl_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:36.614311+00:00
-- url     : https://prove2.me/submissions/a56622b0-bf68-4869-b126-39348f3d7999

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_rd_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
namespace Formalism.FourierDecayAlt.P.Jx2
theorem _root_.solution (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ)
    (hg : 0 < g) : S6.idl E g k ν ≠ 0 := by
  intro h
  have h1 := hN E g k ν hg
  rw [h, map_zero, Rat.cast_zero, Real.sqrt_zero] at h1
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hz1 : (0 : ℝ) < (g : ℝ) ^ k := zpow_pos hg' k
  have hz2 : (0 : ℝ) < S6.rd E ^ ν := zpow_pos (rd_pos E) ν
  have hpos : 0 < ((g : ℝ) ^ k * S6.rd E ^ ν) ^ S6.deg E := pow_pos (mul_pos hz1 hz2) _
  linarith
end Formalism.FourierDecayAlt.P.Jx2
