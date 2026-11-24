-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.stable_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:32.466584+00:00
-- url     : https://prove2.me/submissions/62f54018-d5f4-4dd6-a250-6e9447437728

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution {Q : Ideal (𝓞 K)} (hQ : Q.map (conjO K) = Q) (k : ℕ) :
    ∀ a ∈ Q ^ k, conjO K a ∈ Q ^ k := by
  intro a ha
  have h1 := Ideal.mem_map_of_mem (conjO K) ha
  rwa [Ideal.map_pow, hQ] at h1
end Formalism.HermitianLattices.Ext.L3.NormLifting
