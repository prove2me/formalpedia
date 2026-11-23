-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.exists_prime_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:00.898518+00:00
-- url     : https://prove2.me/submissions/0412055c-c990-4bf4-92dd-1d2abd4ff3e8

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution (P : Ideal (𝓞 K)) [hP : P.IsMaximal] : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ P := by
  have hQ : (P.under ℤ).IsMaximal := Ideal.IsMaximal.under ℤ P
  have hQ0 : P.under ℤ ≠ ⊥ := by
    intro h
    rw [h] at hQ
    exact Int.not_isField (Ring.isField_iff_maximal_bot.2 hQ)
  obtain ⟨p, hp, hpp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hQ.isPrime hQ0
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.1 hpp, ?_⟩
  have hmem : algebraMap ℤ (𝓞 K) p ∈ P := hp
  rcases Int.natAbs_eq p with h | h
  · rw [h] at hmem; simpa using hmem
  · rw [h] at hmem
    have := P.neg_mem hmem
    simpa using this
end Formalism.MainNotions.MassRatioZetaBound
