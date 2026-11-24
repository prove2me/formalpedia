-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:33:03.974067+00:00
-- url     : https://prove2.me/submissions/4d05ad6f-44b6-41d8-a4b1-5869292e5e67

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd


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
theorem _root_.solution (hF : IsFixF K F) {D : K} (hD : star D = D) (h0 : InI 𝔭 0 D) :
    ∃ t δ : 𝓞 F, t ∉ 𝔭 ∧ κ (ι δ) = κ (ι t) * D := by
  obtain ⟨t, ht, z, -, e⟩ := h0
  obtain ⟨δ, hδ⟩ := (conjO_eq_iff_mem_range hF z).1 (by
    apply RingOfIntegers.coe_injective
    show star (κ z) = κ z
    rw [e, star_mul', hD, star_ι hF])
  exact ⟨t, δ, ht, by rw [hδ, e]⟩
end Formalism.HermitianLattices.Ext.L3.Cell
