-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadAdj.rep_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:04:52.201516+00:00
-- url     : https://prove2.me/submissions/d63711ce-ac30-4564-8c99-c3761a7b00d2

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadAdj_rep_eq_zero

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
theorem _root_.solution {a b a' b' : F}
    (h : AdjoinRoot.of (X ^ 2 - C c) a + AdjoinRoot.of _ b * AdjoinRoot.root _ =
      AdjoinRoot.of _ a' + AdjoinRoot.of _ b' * AdjoinRoot.root _) : a = a' ∧ b = b' := by
  have := rep_eq_zero c (a := a - a') (b := b - b') (by
    rw [map_sub, map_sub]; linear_combination h)
  exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩
end Formalism.HermitianLattices.Ext.L3.QuadAdj
