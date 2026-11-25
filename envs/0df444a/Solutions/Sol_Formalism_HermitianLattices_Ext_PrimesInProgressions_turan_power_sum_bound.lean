-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.turan_power_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:30:36.681124+00:00
-- url     : https://prove2.me/submissions/e1fff2bd-3db7-415b-8733-362bafc6e55a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_Turan2Main
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TuranPowerSumBound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_turan2Main


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
theorem _root_.solution : DHTuran2 := by
  refine ⟨1600, 1, by norm_num, le_rfl, fun n m z hn hz hz1 => ?_⟩
  obtain ⟨k, h1, h2, h3⟩ := T2.turan2Main n m z hn hz hz1
  exact ⟨k, h1, by simpa using h2, by simpa using h3⟩
end Formalism.HermitianLattices.Ext.PrimesInProgressions
