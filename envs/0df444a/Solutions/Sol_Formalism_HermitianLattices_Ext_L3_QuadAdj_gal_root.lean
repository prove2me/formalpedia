-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadAdj.gal_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:03.182896+00:00
-- url     : https://prove2.me/submissions/532b3557-e65a-434c-8984-b3cfb4042618

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
variable [Fact (Irreducible (X ^ 2 - C c : F[X]))]
namespace Formalism.HermitianLattices.Ext.L3.QuadAdj
theorem _root_.solution (τ : AdjoinRoot (X ^ 2 - C c) ≃ₐ[F] AdjoinRoot (X ^ 2 - C c)) :
    τ (AdjoinRoot.root _) = AdjoinRoot.root _ ∨ τ (AdjoinRoot.root _) = -AdjoinRoot.root _ := by
  have h := congrArg τ (root_mul_root c)
  have hc : τ (AdjoinRoot.of _ c) = AdjoinRoot.of _ c := τ.commutes c
  rw [map_mul, hc, ← root_mul_root c] at h
  have h2 : (τ (AdjoinRoot.root _) - AdjoinRoot.root (X ^ 2 - C c)) *
      (τ (AdjoinRoot.root _) + AdjoinRoot.root _) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact Or.inl (sub_eq_zero.1 h3)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h3)
end Formalism.HermitianLattices.Ext.L3.QuadAdj
