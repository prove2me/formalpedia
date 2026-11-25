-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.eps_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:16.33887+00:00
-- url     : https://prove2.me/submissions/beb8d771-7949-41c2-b2c1-c7bb611f4fef

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
theorem _root_.solution (n : ℕ) : eps n = if n % 2 = 0 then -1 else 1 := by
  unfold eps Φe
  have h : ((n : ZMod 2) = 0) ↔ n % 2 = 0 := by rw [ZMod.natCast_eq_zero_iff]; omega
  by_cases hn : n % 2 = 0
  · rw [if_pos (h.mpr hn), if_pos hn]
  · rw [if_neg (fun h' => hn (h.mp h')), if_neg hn]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
