-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.mem_fixSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:11.560996+00:00
-- url     : https://prove2.me/submissions/4e61822b-ea6e-4bf3-b6fb-c885c048b83d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {A : Type*} [CommRing A] (σ : A →+* A) (I : Ideal A)
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution {w : A} : w ∈ fixSub σ I ↔ w ∈ I ∧ σ w = w := Iff.rfl
end Formalism.HermitianLattices.Ext.L3.NormLifting
