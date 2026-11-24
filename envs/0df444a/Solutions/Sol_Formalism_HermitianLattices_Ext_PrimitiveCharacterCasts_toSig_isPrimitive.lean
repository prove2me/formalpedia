-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.toSig_isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:31.832364+00:00
-- url     : https://prove2.me/submissions/c75cdc46-013e-43f0-bd4e-de1f155759f8

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
private theorem cast_prim {a b : ℕ} (h : a = b) (χ : DirichletCharacter ℂ a) :
    (cast (congrArg (DirichletCharacter ℂ) h) χ).IsPrimitive ↔ χ.IsPrimitive := by
  subst h; rfl
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
open DirichletCharacter
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
theorem _root_.solution {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) :
    (toSig χ).2.IsPrimitive ↔ χ.IsPrimitive := by
  exact cast_prim (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))).symm χ
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
