-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_entSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:13.11172+00:00
-- url     : https://prove2.me/submissions/5fd9a137-a68a-4cdf-802d-42260265c350

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
theorem _root_.solution {J : Ideal A} {Y : Matrix m r A} : Y ∈ entSub m r J ↔ ∀ i j, Y i j ∈ J := Iff.rfl
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices
