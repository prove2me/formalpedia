-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.mk_form_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:31:10.231958+00:00
-- url     : https://prove2.me/submissions/fdf0d771-b771-47d0-8a0a-880ffa851757

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_conjTranspose_map_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_map_mk_eq_iff

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
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H Y : Matrix κ κ (𝓞 K)) :
    (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ * Hq H 𝔭 k * Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) =
      Hq H 𝔭 k ↔ ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k := by
  rw [conjTranspose_map_mk, ← Matrix.map_mul, ← Matrix.map_mul, map_mk_eq_iff]
end Formalism.HermitianLattices.Ext.L3.HU
