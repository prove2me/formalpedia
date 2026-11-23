-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.toSig_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:32.493038+00:00
-- url     : https://prove2.me/submissions/dc13c55b-1f94-4835-ad77-2538323508f6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
open DirichletCharacter
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
theorem _root_.solution {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : (toSig χ).1 + 1 = n := by
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
