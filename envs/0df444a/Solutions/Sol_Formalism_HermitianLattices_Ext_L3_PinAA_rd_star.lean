-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinAA.rd_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:27:31.843452+00:00
-- url     : https://prove2.me/submissions/4bb725ee-2336-42ce-bea8-202e0ccd7ef5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_rd_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjQ_mk


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
theorem _root_.solution [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k j : ℕ) (a : 𝓞 K ⧸ extP K 𝔭 ^ k) :
    rd K 𝔭 k j (star a) = star (rd K 𝔭 k j a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  show rd K 𝔭 k j (NormLifting.conjQ _ _ (Ideal.Quotient.mk _ a)) =
    NormLifting.conjQ _ _ (rd K 𝔭 k j (Ideal.Quotient.mk _ a))
  rw [rd_mk, NormLifting.conjQ_mk, NormLifting.conjQ_mk, rd_mk]
end Formalism.HermitianLattices.Ext.L3.PinAA
