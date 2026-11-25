-- Prove2me | solution 1 for Formalism.L2.Host.map_eq_mul_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:52.710832+00:00
-- url     : https://prove2.me/submissions/d4be794a-1052-4cbe-b3e9-4ad2a030e343

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RamificationIdxEqOneOfNotDvd
import Theorems.Thm_P2M_Formalism_L2_Host_ramificationIdx__eq_one_29b79749b1e0

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
    (P : Ideal (𝓞 H.E)) [hP : P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    ∃ I : Ideal (𝓞 H.E), (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) = P * I ∧ ¬ I ≤ P := by
  have hle : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.LiesOver.over)
  obtain ⟨I, hI⟩ := (Ideal.dvd_iff_le).2 hle
  refine ⟨I, hI, fun hIP => ?_⟩
  have h1 := ramificationIdx'_eq_one H p hnd P
  have h2 : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≤ P ^ 2 := by
    rw [hI, pow_two]
    exact Ideal.mul_mono_right hIP
  exact (Ideal.ramificationIdx'_ne_one_iff hle).2 h2 h1
end Formalism.L2.Host
