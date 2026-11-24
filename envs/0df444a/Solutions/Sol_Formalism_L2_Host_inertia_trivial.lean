-- Prove2me | solution 1 for Formalism.L2.Host.inertia_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:16:18.443946+00:00
-- url     : https://prove2.me/submissions/75101845-369e-4188-b0f1-e956ace5a540

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RamificationIdxEqOneOfNotDvd
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_frob


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
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) :
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 :=
  (H.der.frob p hnd P).2.2.2 σ
end Formalism.L2.Host
