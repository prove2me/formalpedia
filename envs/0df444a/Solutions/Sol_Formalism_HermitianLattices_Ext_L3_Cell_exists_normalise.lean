-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_normalise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:45.591836+00:00
-- url     : https://prove2.me/submissions/2344c91a-2fc3-432f-b63b-abd680f1c531

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormalise
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_form_smul_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_scale_fixed


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
variable {V : Type} [AddCommGroup V] [Module K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {e : V} (he : e ≠ 0) :
    ∃ μ : K, ∃ a : 𝓞 F, h (μ • e) (μ • e) = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
  have hd0 : h e e ≠ 0 := fun h0 => he (han e h0)
  have hds : star (h e e) = h e e := by
    have e' : starRingEnd K (h e e) = h e e := by
      first
      | exact hs.eq e e
      | exact hs e e
    rwa [starRingEnd_apply] at e'
  obtain ⟨μ, -, hμs, a, ha, ha2⟩ := exists_scale_fixed hF h𝔭 hd0 hds
  exact ⟨μ, a, by rw [form_smul_smul, hμs, ha], ha2⟩
end Formalism.HermitianLattices.Ext.L3.Cell
