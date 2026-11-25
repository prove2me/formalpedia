-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadAdj.gal_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:36.415523+00:00
-- url     : https://prove2.me/submissions/42db681f-4ff5-44f7-b6c0-751bdeba67e7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadAdj_conj_root
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadAdj_gal_root

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
variable [Fact (Irreducible (X ^ 2 - C c : F[X]))]
namespace Formalism.HermitianLattices.Ext.L3.QuadAdj
theorem _root_.solution (τ : AdjoinRoot (X ^ 2 - C c) ≃ₐ[F] AdjoinRoot (X ^ 2 - C c)) :
    τ = 1 ∨ τ = conj c := by
  rcases gal_root c τ with h | h
  · left
    apply AlgEquiv.coe_toAlgHom_injective
    exact AdjoinRoot.algHom_ext h
  · right
    apply AlgEquiv.coe_toAlgHom_injective
    exact AdjoinRoot.algHom_ext (h.trans (conj_root c).symm)
end Formalism.HermitianLattices.Ext.L3.QuadAdj
