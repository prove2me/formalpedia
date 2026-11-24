-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinAA.map_smul_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:27:18.856594+00:00
-- url     : https://prove2.me/submissions/9a26394e-7a3a-4332-9a8b-ec1d99715dfd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff

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
variable {κ : Type} [Fintype κ] [DecidableEq κ] [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.PinAA
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) (c : 𝓞 F) (H : Matrix κ κ (𝓞 K)) :
    (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) =
      Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) • H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  ext i j
  show Ideal.Quotient.mk _ (ι c * H i j) =
    Ideal.Quotient.mk _ (ι c) * Ideal.Quotient.mk _ (H i j)
  exact map_mul _ _ _
end Formalism.HermitianLattices.Ext.L3.PinAA
