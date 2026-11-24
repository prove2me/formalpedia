-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.toSig_level_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:32.034372+00:00
-- url     : https://prove2.me/submissions/10cf8600-f939-462f-b038-61e8cdfeb347

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_toSig_fst

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
theorem _root_.solution {n m : ℕ} [NeZero n] [NeZero m] (χ : DirichletCharacter ℂ n) (ψ : DirichletCharacter ℂ m)
    (h : toSig χ = toSig ψ) : n = m := by
  have h1 := congrArg Sigma.fst h
  have hn := toSig_fst χ
  have hm := toSig_fst ψ
  omega
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
