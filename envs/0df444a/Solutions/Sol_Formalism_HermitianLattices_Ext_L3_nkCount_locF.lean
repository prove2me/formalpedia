-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.nkCount_locF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:55.625569+00:00
-- url     : https://prove2.me/submissions/29c1773a-d74c-42b0-bea0-0cb4efad58fb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_nkCount_locF


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F) : nkCount h (locF 𝔭 L) 𝔭 k n = nkCount h L 𝔭 k n :=
  localizedQuotients.nkCount_locF hF h L 𝔭 h𝔭 k n
end Formalism.HermitianLattices.Ext.L3
