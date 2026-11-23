-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadAdj.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:52.242328+00:00
-- url     : https://prove2.me/submissions/2dc93ee5-1594-4a0c-b084-f4dbb3fbb230

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
theorem _root_.solution (y : AdjoinRoot (X ^ 2 - C c)) :
    ∃ a b : F, y = AdjoinRoot.of _ a + AdjoinRoot.of _ b * AdjoinRoot.root _ := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective y
  have h1 : AdjoinRoot.mk (X ^ 2 - C c) f = AdjoinRoot.mk (X ^ 2 - C c) (f %ₘ (X ^ 2 - C c)) := by
    rw [AdjoinRoot.mk_eq_mk, modByMonic_eq_sub_mul_div]
    exact ⟨f /ₘ (X ^ 2 - C c), by ring⟩
  have h2 : (f %ₘ (X ^ 2 - C c)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt f (monic_pol c) (by
      intro h
      have := natDegree_pol c
      rw [h, natDegree_one] at this
      omega)
    rw [natDegree_pol] at this
    omega
  obtain ⟨b, a, hab⟩ := exists_eq_X_add_C_of_natDegree_le_one h2
  refine ⟨a, b, ?_⟩
  rw [h1, hab, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, add_comm]
end Formalism.HermitianLattices.Ext.L3.QuadAdj
