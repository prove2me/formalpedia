-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_sum_cpow_sub_prim_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:12:36.394491+00:00
-- url     : https://prove2.me/submissions/329a1469-4006-471f-a19b-10c3f67b3a5f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_cpow_sub_prim_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution {U : ℕ} (hU : 1 ≤ U) {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 - w ≠ 0)
    (V : ℕ) (hV : U ≤ V) :
    ‖∑ n ∈ Ioc U V, (n : ℂ) ^ (-w) - ((V : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      ((V : ℝ) - U) * (‖w‖ / U) := by
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hV ih =>
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    rw [Finset.sum_Ioc_succ_top (by omega : U ≤ V)]
    have hstep := norm_cpow_sub_prim_le (i := V) (by omega) hw hw1
    have hstep' : ‖((V + 1 : ℕ) : ℂ) ^ (-w) -
        (((V + 1 : ℕ) : ℂ) ^ (1 - w) - (V : ℂ) ^ (1 - w)) / (1 - w)‖ ≤ ‖w‖ / U := by
      refine hstep.trans ?_
      exact div_le_div_of_nonneg_left (norm_nonneg _) hU0 (by exact_mod_cast hV)
    have hsplit : ∑ n ∈ Ioc U V, (n : ℂ) ^ (-w) + ((V + 1 : ℕ) : ℂ) ^ (-w) -
        (((V + 1 : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w) =
        (∑ n ∈ Ioc U V, (n : ℂ) ^ (-w) - ((V : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w)) +
        (((V + 1 : ℕ) : ℂ) ^ (-w) -
          (((V + 1 : ℕ) : ℂ) ^ (1 - w) - (V : ℂ) ^ (1 - w)) / (1 - w)) := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ((add_le_add ih hstep').trans (le_of_eq ?_))
    push_cast; ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
