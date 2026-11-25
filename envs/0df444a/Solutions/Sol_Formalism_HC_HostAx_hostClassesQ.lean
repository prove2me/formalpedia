-- Prove2me | solution 1 for Formalism.HC.HostAx.hostClassesQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:58.826192+00:00
-- url     : https://prove2.me/submissions/acca766b-5667-46bf-b255-798b29c09586

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_HostRaw_PsQ_psAt_prime
import Theorems.Thm_Formalism_HC_HostAx_hostClasses
import Theorems.Thm_Formalism_FrobeniusOrbits_hostClasses


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
namespace Formalism.HC.HostAx
theorem _root_.solution (hP : H.PsQ) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    (((H.galE σ).1 = 1 ∨ (H.galE σ).1 = (-1, 1)) ↔ jacobiSym (-(H.d : ℤ)) p = 1) ∧
    ((H.galE σ).1 = (1, -1) ↔ (jacobiSym (-(H.d : ℤ)) p = -1 ∧ jacobiSym (-(H.q : ℤ)) p = 1)) ∧
    ((H.galE σ).1 = c0 ↔ (jacobiSym (-(H.d : ℤ)) p = -1 ∧ jacobiSym (-(H.q : ℤ)) p = -1)) := by
  have h := H.hostClasses p hp P σ hσ
  rw [hP.psAt_prime Fact.out hp] at h
  exact h
end Formalism.HC.HostAx
