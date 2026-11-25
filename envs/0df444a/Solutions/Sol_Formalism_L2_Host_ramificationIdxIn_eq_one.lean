-- Prove2me | solution 1 for Formalism.L2.Host.ramificationIdxIn_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:17.724638+00:00
-- url     : https://prove2.me/submissions/c199bd86-0143-4e02-b244-7bb2372c652b

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RamificationIdxEqOneOfNotDvd
import Theorems.Thm_Formalism_L2_Host_span_isPrime
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
theorem _root_.solution (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN) :
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 H.E) = 1 := by
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  have hne : (span {(p : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI : (span {(p : ℤ)}).IsPrime := span_isPrime p
  haveI : (span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 H.E) (span {(p : ℤ)})
  haveI := hQm.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) Q (H.E ≃ₐ[ℚ] H.E),
    ← Formalism.TwoAdicCyclotomicDecomposition.odd_card H.E p Q]
  have hbot : Q.inertia (H.E ≃ₐ[ℚ] H.E) = ⊥ := by
    ext σ
    rw [Subgroup.mem_bot]
    exact AddSubgroup.mem_inertia.trans (inertia_trivial H p hnd Q σ)
  rw [hbot, Subgroup.card_bot]
end Formalism.L2.Host
