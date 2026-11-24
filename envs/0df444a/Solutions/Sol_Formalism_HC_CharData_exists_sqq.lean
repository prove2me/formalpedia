-- Prove2me | solution 1 for Formalism.HC.CharData.exists_sqq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:35:08.364705+00:00
-- url     : https://prove2.me/submissions/64f3ddbf-f64f-498e-9cf1-7a525d9d657a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.CharData
variable {φ : Frame} (D : CharData φ)
namespace Formalism.HC.CharData
theorem _root_.solution (h : D.toHostRaw.PsQ) : ∃ s : D.toHostRaw.E, s ^ 2 = -(D.toHostRaw.q : D.toHostRaw.E) ∧
    ∀ σ : D.toHostRaw.E ≃ₐ[ℚ] D.toHostRaw.E, σ s = ((((D.toHostRaw.gal σ).1.1 : ℤˣ) : ℤ) : D.toHostRaw.E) * s :=
  D.exists_root D.hyp.1 (by have := D.hyp.2.2.1; omega) (Dvd.dvd.mul_right (dvd_mul_left _ _) _) φ.chQ h
end Formalism.HC.CharData
