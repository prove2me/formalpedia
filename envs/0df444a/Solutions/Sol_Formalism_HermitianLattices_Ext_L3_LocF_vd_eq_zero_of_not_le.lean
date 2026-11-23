-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.vd_eq_zero_of_not_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:01.367449+00:00
-- url     : https://prove2.me/submissions/6f73cfc5-f099-4f93-ae19-c4adae573a64

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (hn : ¬ discrIdeal h L ≤ extP K 𝔭) : vd h L 𝔭 = 0 := by
  unfold vd
  have h1 : {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} = {0} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro he
      by_contra h0
      exact hn (he.trans (Ideal.pow_le_self h0))
    · rintro rfl
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
  rw [h1, csSup_singleton]
end Formalism.HermitianLattices.Ext.L3.LocF
