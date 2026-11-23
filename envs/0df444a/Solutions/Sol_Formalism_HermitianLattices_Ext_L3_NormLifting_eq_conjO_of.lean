-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.eq_conjO_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:35.202795+00:00
-- url     : https://prove2.me/submissions/f44569e9-61d7-42eb-9b75-723f8cacd7e8

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
theorem _root_.solution {θ t : 𝓞 K} (h : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ)) :
    t = conjO K θ := by
  apply RingOfIntegers.ext
  have h' : (t : K) = star (θ : K) := h
  rw [h']
  first
  | rfl
  | simp [conjO]
  | (unfold conjO; simp)
end Formalism.HermitianLattices.Ext.L3.NormLifting
