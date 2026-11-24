-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinAA.card_ker_rd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:27:13.595502+00:00
-- url     : https://prove2.me/submissions/ffdfd651-a1bf-4136-808d-3f015af4495d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_rd_surjective
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_absNorm_extP_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_absNorm_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinAA
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans localValuationFiltration
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.PinAA
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k j : ℕ} (hjk : j ≤ k) :
    Nat.card (RingHom.ker (rd K 𝔭 k j)) = Ideal.absNorm 𝔭 ^ (2 * j) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (RingHom.ker (rd K 𝔭 k j))
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective (rd_surjective 𝔭 k j)).toEquiv,
    idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭, idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭] at h1
  have hpos : 0 < Ideal.absNorm 𝔭 ^ (2 * (k - j)) := pow_pos (reductionMapsOfForms.absNorm_pos h𝔭) _
  have h2 : Ideal.absNorm 𝔭 ^ (2 * k) = Ideal.absNorm 𝔭 ^ (2 * j) * Ideal.absNorm 𝔭 ^ (2 * (k - j)) := by
    rw [← pow_add]; congr 1; omega
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← h1])).symm
end Formalism.HermitianLattices.Ext.L3.PinAA
