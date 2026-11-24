-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.EndomorphismScalars.end_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:51.280078+00:00
-- url     : https://prove2.me/submissions/7bd2d89c-e32a-43df-8bf8-5d9da8d5014f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealLeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_EndomorphismScalars_mk_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V}
namespace Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ)
    (X : Module.End (𝓞 K) (Qk L 𝔭 k)) :
    ∃ b : 𝓞 K, algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = X := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (X (Submodule.Quotient.mk ⟨e, he.1⟩))
  obtain ⟨a, ha⟩ := mk_eq_smul h𝔭 he k y
  refine ⟨a, LinearMap.ext fun z => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨ax, hax⟩ := mk_eq_smul h𝔭 he k x
  rw [Module.algebraMap_end_apply, hax, map_smul, ← hy, ha, smul_comm]
end Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
