-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.pow_smul_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:41.958078+00:00
-- url     : https://prove2.me/submissions/57cd91ad-c1d0-4d44-b05c-52c6301366e7

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
namespace Formalism.NG.IdemLiftAlt
theorem _root_.solution (I : Ideal O) {i j : ℕ} (h : i ≤ j) {x : A}
    (hx : x ∈ I ^ j • (⊤ : Submodule O A)) : x ∈ I ^ i • (⊤ : Submodule O A) :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h) hx
end Formalism.NG.IdemLiftAlt
