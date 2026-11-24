-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinAA.mul_eq_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:59:18.88932+00:00
-- url     : https://prove2.me/submissions/6765b727-9926-46d1-983c-b40bbc9a7b9d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_mul_eq_zero_iff

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ}
    (hk : vF 𝔭 c ≤ k) (x y : 𝓞 K ⧸ extP K 𝔭 ^ k) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) * x = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) * y ↔
      rd K 𝔭 k (vF 𝔭 c) x = rd K 𝔭 k (vF 𝔭 c) y := by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero_iff h𝔭 hc hk, map_sub, sub_eq_zero]
end Formalism.HermitianLattices.Ext.L3.PinAA
