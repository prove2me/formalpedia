-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.map_factor_map_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:42:56.428705+00:00
-- url     : https://prove2.me/submissions/d361e60d-48a0-4fd5-9b90-e254b1cbdb03

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm

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
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) {j k : ℕ} (hjk : j ≤ k) (Y : Matrix κ κ (𝓞 K)) :
    (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))).map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right hjk)) = Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ j)) := by
  ext i l
  rfl
end Formalism.HermitianLattices.Ext.L3.HU
