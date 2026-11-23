-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_floor_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:29.958251+00:00
-- url     : https://prove2.me/submissions/f6eafbb3-ed15-461d-a240-c7f69cf4f7a8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {v w : ℕ} (h : v ≤ w) :
    ⌊Real.exp (v : ℝ)⌋₊ ≤ ⌊Real.exp (w : ℝ)⌋₊ :=
  Nat.floor_mono (Real.exp_le_exp.mpr (by exact_mod_cast h))
end Formalism.HermitianLattices.Ext.PrimesInProgressions
