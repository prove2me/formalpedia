-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_sgn_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:04:05.004571+00:00
-- url     : https://prove2.me/submissions/b2e2ab32-d12e-4d89-85f3-bb77f9d5247f

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_intCast_mem_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_natCast_not_mem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_lift
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_smul_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {L : Type} [Field L] [NumberField L] (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})]
    (σ : Gal(L/ℚ)) (hσ : ∀ x : 𝓞 L, σ • x - x ∈ P) (y : L) (s : ℕ)
    (hy : y ^ 2 = ((-(s : ℤ) : ℤ) : L)) (hrs : ¬ r ∣ s) : sgn σ y = 1 := by
  rcases Int.units_eq_one_or (sgn σ y) with h | h
  · exact h
  · exfalso
    obtain ⟨Y, hYc, hY2⟩ := odd_lift y _ hy
    have hσY := odd_smul_lift σ y _ hy Y hYc
    rw [h] at hσY
    have h2Y : (2 : 𝓞 L) * Y ∈ P := by
      have := P.neg_mem_iff.mpr (hσ Y)
      rw [hσY] at this
      convert this using 1
      push_cast
      ring
    have h2 : (2 : 𝓞 L) ∉ P := by
      have := odd_natCast_not_mem r P 2
        (fun hd => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd))
      exact_mod_cast this
    have hYP : Y ∈ P := ((inferInstance : P.IsPrime).mem_or_mem h2Y).resolve_left h2
    have hsP : ((-(s : ℤ) : ℤ) : 𝓞 L) ∈ P := by
      rw [← hY2]
      exact P.pow_mem_of_mem hYP 2 (by norm_num)
    rw [odd_intCast_mem_iff r P, dvd_neg] at hsP
    exact hrs (by exact_mod_cast hsP)
end Formalism.TwoAdicCyclotomicDecomposition
