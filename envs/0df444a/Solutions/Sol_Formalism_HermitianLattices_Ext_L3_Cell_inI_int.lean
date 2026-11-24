-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.inI_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:47:21.99687+00:00
-- url     : https://prove2.me/submissions/022b9c70-e10e-48ba-b653-ad0522e625f4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_congrP_iff_inI
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_congrP_int


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
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {z : 𝓞 K} : InI 𝔭 k (κ z) ↔ z ∈ extP K 𝔭 ^ k := by
  have := integralBasisSpans.congrP_int h𝔭 k z 0
  rw [congrP_iff_inI, map_zero, sub_zero, Ideal.Quotient.eq, sub_zero] at this
  exact this
end Formalism.HermitianLattices.Ext.L3.Cell
