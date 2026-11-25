-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_round_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:57.801224+00:00
-- url     : https://prove2.me/submissions/ad27e9ee-9a8e-4fc1-b050-ba65fd26fdf9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLocL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (x : ℝ) (n : ℤ) (h : |x| ≤ n) : |round x| ≤ n := by
  have h1 := abs_sub_round x
  have h2 : ((|round x| : ℤ) : ℝ) < (n : ℝ) + 1 := by
    rw [Int.cast_abs]
    have h3 : |(round x : ℝ)| ≤ |x| + |x - round x| := by
      have h4 := abs_sub_abs_le_abs_sub (round x : ℝ) x
      rw [abs_sub_comm] at h4
      linarith
    linarith
  have h3 : |round x| < n + 1 := by exact_mod_cast h2
  exact Int.lt_add_one_iff.1 h3
end Formalism.HermitianLattices.Ext.PrimesInProgressions
