-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Hq_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:16.649196+00:00
-- url     : https://prove2.me/submissions/7a1f6ba2-46f3-4ee2-b222-6b8921d24b21

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open HermitianSublattices idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {H : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (Hq H 𝔭 k)ᴴ = Hq H 𝔭 k := by
  conv_rhs => rw [← hH]
  exact (conjTranspose_map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) (fun a => (star_mk 𝔭 k a).symm)).symm
end Formalism.HermitianLattices.Ext.L3.HU
