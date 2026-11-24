-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:31:23.849926+00:00
-- url     : https://prove2.me/submissions/70282eec-230c-4755-b695-8926acb6a0fa

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Finite (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))) := by
  have : Module.Finite (𝓞 K) ↥A₀ := Module.Finite.iff_fg.2 hA₀.fg
  have : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := idealPowerSpanBounds.finite_quot h𝔭 k
  have : Module.Finite (𝓞 K ⧸ extP K 𝔭 ^ k)
      (↥A₀ ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A₀)) :=
    Module.Finite.of_restrictScalars_finite (𝓞 K) _ _
  have : Finite (↥A₀ ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A₀)) :=
    Module.finite_of_finite (𝓞 K ⧸ extP K 𝔭 ^ k)
  exact Finite.of_equiv _ (localizedQuotients.quotLocF h𝔭 A₀ k).toEquiv
end Formalism.HermitianLattices.Ext.L3.LIOrb
