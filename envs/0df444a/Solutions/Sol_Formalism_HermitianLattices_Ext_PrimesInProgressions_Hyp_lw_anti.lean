-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.lw_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:46:42.872949+00:00
-- url     : https://prove2.me/submissions/3fb6deb0-5aa2-4329-b07f-18eaf5f33f31

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_lw_nonneg

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (n : ℕ) (hn : 3 ≤ n) : 0 ≤ lw (n + 1) ∧ lw (n + 1) ≤ lw n := by
  refine ⟨lw_nonneg _, ?_⟩
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ (n : ℝ) := by
    have := Real.exp_one_lt_d9; linarith
  unfold lw
  push_cast
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (by linarith)) (by linarith)
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
