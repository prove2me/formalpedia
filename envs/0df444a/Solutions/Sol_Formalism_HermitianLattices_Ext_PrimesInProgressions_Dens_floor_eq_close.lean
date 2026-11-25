-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.floor_eq_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:31:52.06768+00:00
-- url     : https://prove2.me/submissions/d7517a72-cfbc-4c7c-8d9f-df8af7e10e74

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace

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
theorem _root_.solution {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ⌊a⌋₊ = ⌊b⌋₊) : |a - b| < 1 := by
  have h1 := Nat.floor_le ha
  have h2 := Nat.lt_floor_add_one a
  have h3 := Nat.floor_le hb
  have h4 := Nat.lt_floor_add_one b
  rw [h] at h1 h2
  rw [abs_lt]; constructor <;> linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
