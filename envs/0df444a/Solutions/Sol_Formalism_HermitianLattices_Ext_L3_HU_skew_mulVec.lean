-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.skew_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:56.737808+00:00
-- url     : https://prove2.me/submissions/c0b0b84d-6fee-4d8a-a749-9067e3f644e9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk

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
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {A : Type*} [CommRing A] [StarRing A] (M N : Matrix κ κ A) (u v : κ → A) :
    star (M *ᵥ u) ⬝ᵥ (N *ᵥ v) + star u ⬝ᵥ (N *ᵥ (M *ᵥ v)) = star u ⬝ᵥ ((Mᴴ * N + N * M) *ᵥ v) := by
  rw [add_mulVec, dotProduct_add, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
end Formalism.HermitianLattices.Ext.L3.HU
