-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.linPart_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:07.607147+00:00
-- url     : https://prove2.me/submissions/ddbe0e30-92f6-45e4-9b0f-c76f817321ec

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
variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution (I : Ideal A) {M : ℕ} (y : Fin M → A) (δ : Fin M → I) :
    linPart σ I y δ = ∑ i, (σ (y i) * (δ i : A) + σ (δ i) * y i) := rfl
end Formalism.HermitianLattices.Ext.L3.NormLifting
