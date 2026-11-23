-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.conjO_conjO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:49.897434+00:00
-- url     : https://prove2.me/submissions/5b000b34-0c43-4739-8fd6-2f5fc73a4d6f

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
theorem _root_.solution (x : 𝓞 K) : conjO K (conjO K x) = x := by
  first
  | exact RingOfIntegers.ext (star_star (x : K))
  | (apply RingOfIntegers.ext; simp [conjO])
  | (apply RingOfIntegers.ext; unfold conjO; simp)
end Formalism.HermitianLattices.Ext.L3.NormLifting
