-- Prove2me | solution 1 for Formalism.HC.dvd_discr_of_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:52:10.534136+00:00
-- url     : https://prove2.me/submissions/761fd97b-497d-4a3b-bcbd-f6a87f5db063

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Theorems.Thm_Formalism_HC_dvd_discr_of_mem_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Ideal
noncomputable section
open Formalism Formalism.HC
namespace Formalism.HC
theorem _root_.solution (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {a : E} (ha : a ^ 2 = -(p : E)) :
    (p : ℤ) ∣ discr E := by
  have hi : IsIntegral ℤ a := IsIntegral.of_pow two_pos (ha ▸ (isIntegral_natCast p).neg)
  let b : 𝓞 E := ⟨a, hi⟩
  have hb : b ^ 2 = -(p : 𝓞 E) := RingOfIntegers.ext (by
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast]; exact ha)
  refine dvd_discr_of_mem_sq E hp fun P hP hv => ?_
  have h1 : b ∈ P := hP.mem_of_pow_mem 2 (hb ▸ P.neg_mem hv)
  have h2 := (P ^ 2).neg_mem (Ideal.pow_mem_pow h1 2)
  rwa [hb, neg_neg] at h2
end Formalism.HC
