-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.tp_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:53.594478+00:00
-- url     : https://prove2.me/submissions/018ff383-494b-49e6-b0ed-3034dfe30b49

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_tp_eval
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_tp_eval_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
theorem _root_.solution (n : ℕ) (z : Fin n → ℂ) (i : Fin n) :
    ∑ a ∈ range (n + 1), (tp n z).coeff a * z i ^ a = 0 := by
  rw [← tp_eval_sum, tp_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
