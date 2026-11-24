-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_scale_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:36:36.720878+00:00
-- url     : https://prove2.me/submissions/ecfbf338-4481-4044-81be-13349521f1de

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_scale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_mem_pow_vF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF


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
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a₁ : 𝓞 F} (h0 : a₁ ≠ 0) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * κ (ι a₁) = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
  have h1 := localValuationFiltration.mem_pow_vF h𝔭 h0
  have h2 := localValuationFiltration.notMem_pow_vF h𝔭 h0
  have e : vF 𝔭 a₁ = vF 𝔭 a₁ / 2 + vF 𝔭 a₁ / 2 + vF 𝔭 a₁ % 2 := by omega
  rw [e] at h1 h2
  obtain ⟨μ, hμ0, hμs, a, ha, ha'⟩ := exists_scale (K := K) hF h𝔭 h1 h2
  exact ⟨μ, hμ0, hμs, a, ha, fun hm => ha' (Ideal.pow_le_pow_right (by omega) hm)⟩
end Formalism.HermitianLattices.Ext.L3.Cell
