-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.aniso_of_totPosDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:07.560796+00:00
-- url     : https://prove2.me/submissions/37ef1f68-50f8-4941-8f36-51c9765943a3

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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x, h x x = 0 → x = 0 := by
  intro x hx
  by_contra hne
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := hd x hne φ
  rw [hx, map_zero] at this
  simp at this
end Formalism.HermitianLattices.Ext.L3.LocF
