-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.charSum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:33:38.00821+00:00
-- url     : https://prove2.me/submissions/7ef4e9a5-3e72-4f05-8725-0c5c048d85d3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_character_sum_Icc_le


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
theorem _root_.solution (hχ : χ ≠ 1) (m : ℕ) : ‖∑ n ∈ Ioc 0 m, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have e : Icc 1 m = Ioc 0 m := by ext x; simp; omega
  have := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ m
  rwa [e] at this
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
