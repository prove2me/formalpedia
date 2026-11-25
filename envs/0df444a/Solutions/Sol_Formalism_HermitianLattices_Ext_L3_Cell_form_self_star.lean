-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.form_self_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:27:25.640488+00:00
-- url     : https://prove2.me/submissions/166c4b90-1199-4bab-8b80-d05172df35cc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNearRepresentation

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (w : V) : star (h w w) = h w w :=
  hs.eq w w
end Formalism.HermitianLattices.Ext.L3.Cell
