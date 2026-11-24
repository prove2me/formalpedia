-- Prove2me | solution 1 for Formalism.L2.Host.ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:33:34.737817+00:00
-- url     : https://prove2.me/submissions/65dde4f8-a7fd-4b31-923f-b4c1fc707141

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RamificationIdxEqOneOfNotDvd
import Theorems.Thm_Formalism_L2_Host_inertia_trivial
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_inertia_trivial
import Theorems.Thm_Formalism_FrobeniusOrbits_hostE_isGalois
import Theorems.Thm_Formalism_HC_HostAx_hostE_isGalois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Ideal
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.BasicNotions Formalism.FrobeniusOrbits
variable {R : Ranks} (H : Formalism.BasicNotions.Host R)
namespace Formalism.L2.Host
theorem _root_.solution (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] : P.ramificationIdx ℤ = 1 := by
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  have hbot : P.inertia (H.E ≃ₐ[ℚ] H.E) = ⊥ := by
    ext σ
    rw [Subgroup.mem_bot]
    exact AddSubgroup.mem_inertia.trans (inertia_trivial H p hnd P σ)
  rw [← Formalism.TwoAdicCyclotomicDecomposition.odd_card H.E p P, hbot, Subgroup.card_bot]
end Formalism.L2.Host
