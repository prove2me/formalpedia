-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.toSig_LFunction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:31.519093+00:00
-- url     : https://prove2.me/submissions/eb3a1cc1-ffc2-41e3-82ec-d8aead7ea84a

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
section
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
open DirichletCharacter
private theorem cast_L {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) (χ : DirichletCharacter ℂ a) (s : ℂ) :
    DirichletCharacter.LFunction (cast (congrArg (DirichletCharacter ℂ) h) χ) s = DirichletCharacter.LFunction χ s := by
  subst h; rfl
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
open DirichletCharacter
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
theorem _root_.solution {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (s : ℂ) :
    DirichletCharacter.LFunction (toSig χ).2 s = DirichletCharacter.LFunction χ s := by
  exact cast_L (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))).symm χ s
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
