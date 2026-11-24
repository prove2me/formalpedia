-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_scale_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:52:58.507123+00:00
-- url     : https://prove2.me/submissions/698ed8b8-3e18-4023-abb8-2740721e09f6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_scale_int
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsUnif0_ne_zero
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {d : K} (hd0 : d ≠ 0)
    (hds : star d = d) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * d = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
  obtain ⟨f, rfl⟩ := (hF d).1 hds
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hκy := κι_ne_zero (K := K) hy0
  have e : algebraMap F K (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y) = κ (ι x) / κ (ι y) := by
    rw [map_div₀]; rfl
  rw [e] at hd0 ⊢
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hd0
    simp
  obtain ⟨μ, hμ0, hμs, a, ha, ha'⟩ := exists_scale_int (K := K) hF h𝔭 (mul_ne_zero hy0 hx0)
  refine ⟨μ * κ (ι y), mul_ne_zero hμ0 hκy, by rw [star_mul', hμs, star_ι hF], a, ?_, ha'⟩
  rw [← ha, map_mul ι, map_mul κ]
  field_simp
end Formalism.HermitianLattices.Ext.L3.Cell
