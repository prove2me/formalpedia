-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadAdj.rep_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:03.899649+00:00
-- url     : https://prove2.me/submissions/5d5a38f5-808f-4baf-98e4-2f9c6d86f6c9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.QuadAdj
variable {F : Type*} [Field F] (c : F)
namespace Formalism.HermitianLattices.Ext.L3.QuadAdj
theorem _root_.solution {a b : F}
    (h : AdjoinRoot.of (X ^ 2 - C c) a + AdjoinRoot.of _ b * AdjoinRoot.root _ = 0) :
    a = 0 ∧ b = 0 := by
  have h1 : AdjoinRoot.mk (X ^ 2 - C c) (C b * X + C a) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, add_comm]
    exact h
  by_contra hne
  have h0 : (C b * X + C a : F[X]) ≠ 0 := by
    intro h0
    apply hne
    have ha := congrArg (fun p => coeff p 0) h0
    have hb := congrArg (fun p => coeff p 1) h0
    simp at ha hb
    exact ⟨ha, hb⟩
  refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_pol c) h0 ?_ h1
  rw [natDegree_pol]
  exact lt_of_le_of_lt natDegree_linear_le one_lt_two
end Formalism.HermitianLattices.Ext.L3.QuadAdj
