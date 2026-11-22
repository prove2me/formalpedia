-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:37.872193+00:00
-- url     : https://prove2.me/submissions/1c18a9da-9b1a-4178-9376-635f22be1823

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices
open Matrix
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
namespace Formalism.HermitianLattices.Ext.L3.HermitianSublattices
theorem _root_.solution {J : Ideal A} {S : Matrix r r A} :
    S ∈ hermSub r J ↔ Sᴴ = S ∧ ∀ i j, S i j ∈ J := Iff.rfl
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices
