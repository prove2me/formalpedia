-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.VecSplit.comb_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:21.243945+00:00
-- url     : https://prove2.me/submissions/dbfa7b3f-c6c9-474e-8bd6-6393dfd62aa7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_h_x__comb_726bcd8e9864

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open Formalism.HermitianLattices.Ext.L3.VecSplit
variable (S : VecSplit h h')
namespace Formalism.HermitianLattices.Ext.L3.VecSplit
theorem _root_.solution {c c' : K} {a a' : V'} :
    c • S.x₀ + S.ι a = c' • S.x₀ + S.ι a' ↔ c = c' ∧ a = a' := by
  constructor
  · intro he
    have hc : c = c' := by
      have := congrArg (h S.x₀) he
      rw [S.h_x₀_comb, S.h_x₀_comb] at this
      exact mul_right_cancel₀ S.hx₀ this
    subst hc
    exact ⟨rfl, S.inj (add_left_cancel he)⟩
  · rintro ⟨rfl, rfl⟩
    rfl
end Formalism.HermitianLattices.Ext.L3.VecSplit
