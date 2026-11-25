-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.inRegion_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:41:57.754887+00:00
-- url     : https://prove2.me/submissions/8674f130-91eb-4f89-b080-8fb3ed9d6ddd

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
theorem _root_.solution {c c' : ℝ} (hc : c ≤ c') (q : ℕ) [NeZero q] (s : ℂ) (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at hs ⊢
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_pos (by nlinarith [abs_nonneg s.im])
  have h1 : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c' / Real.log ((q : ℝ) * (|s.im| + 2)) :=
    div_le_div_of_nonneg_right hc hlog.le
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
