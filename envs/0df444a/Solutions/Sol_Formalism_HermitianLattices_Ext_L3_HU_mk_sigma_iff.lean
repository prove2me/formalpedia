-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.mk_sigma_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:38.658323+00:00
-- url     : https://prove2.me/submissions/04335acd-667c-46fc-aafd-e446a54babe2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_conjTranspose_map_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_map_mk_eq_iff
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



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
    Hq H 𝔭 k * Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) +
      (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ * Hq H 𝔭 k = 0 ↔
      ∀ i j, (Yᴴ * H + H * Y) i j ∈ extP K 𝔭 ^ k := by
  have h0 : (0 : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k)) =
      (0 : Matrix κ κ (𝓞 K)).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
    ext i j
    simp
  rw [conjTranspose_map_mk, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _), h0,
    map_mk_eq_iff, sub_zero, add_comm]
end Formalism.HermitianLattices.Ext.L3.HU
