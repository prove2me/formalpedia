-- Prove2me | solution 1 for Formalism.HC.HostRaw.fix_thM_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:14:49.253635+00:00
-- url     : https://prove2.me/submissions/dc2bf08f-b53d-441d-ad28-af283b5cf173

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_HC_HostRaw_adjoin_thM

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
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution (m : ℕ) (σ : H.E ≃ₐ[ℚ] H.E) : σ (H.thM m) = H.thM m ↔ σ ∈ H.congrGal m := by
  rw [← fixingSubgroup_fixedField (H.congrGal m), ← H.adjoin_thM, IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun h x hx => ?_, fun h => h _ (mem_adjoin_simple_self _ _)⟩
  have : ℚ⟮H.thM m⟯ ≤ fixedField (Subgroup.zpowers σ) := by
    rw [adjoin_simple_le_iff, mem_fixedField_iff]
    intro τ hτ
    exact (Subgroup.zpowers_le.2 (show σ ∈ MulAction.stabilizer _ (H.thM m) from h)) hτ
  exact (mem_fixedField_iff _ _).1 (this hx) σ (Subgroup.mem_zpowers σ)
end Formalism.HC.HostRaw
