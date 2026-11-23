-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mem_idQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:26.782805+00:00
-- url     : https://prove2.me/submissions/d1465e30-f94c-464d-9a0e-b89bce3770d8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {k j : ℕ} {a : 𝓞 K ⧸ extP K 𝔭 ^ k} :
    a ∈ idQ K 𝔭 k j ↔ ∃ z ∈ extP K 𝔭 ^ j, Ideal.Quotient.mk _ z = a := by
  show a ∈ (extP K 𝔭 ^ j).map (Ideal.Quotient.mk _) ↔ _
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
