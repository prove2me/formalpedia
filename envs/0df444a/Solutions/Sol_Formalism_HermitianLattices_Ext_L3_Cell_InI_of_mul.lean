-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.InI.of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:30:53.141001+00:00
-- url     : https://prove2.me/submissions/026c2374-b18c-4d8a-87d4-49a899262ea1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI

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
namespace InI
theorem _root_.solution (hp : 𝔭.IsPrime) {k : ℕ} {t : 𝓞 F} (ht : t ∉ 𝔭) {a : K}
    (h : InI 𝔭 k (κ (ι t) * a)) : InI 𝔭 k a := by
  obtain ⟨u, hu, z, hz, e⟩ := h
  exact ⟨u * t, fun h => (hp.mem_or_mem h).elim hu ht, z, hz, by rw [e, map_mul, map_mul, mul_assoc]⟩
end InI
end Formalism.HermitianLattices.Ext.L3.Cell
