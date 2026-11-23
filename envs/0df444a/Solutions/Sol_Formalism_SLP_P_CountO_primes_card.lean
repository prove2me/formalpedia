-- Prove2me | solution 1 for Formalism.SLP.P.CountO.primes_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:36.889088+00:00
-- url     : https://prove2.me/submissions/ee9508dc-6bd0-453f-b27c-288da5e3d09c

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
namespace Formalism.SLP.P.CountO
theorem _root_.solution (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    ∃ Ps : Finset (Ideal (𝓞 E)), Ps.card ≤ finrank ℚ E ∧
      ∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : ℕ) : 𝓞 E) ∈ P → P ∈ Ps := by
  classical
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simp [hp.ne_zero]
  refine ⟨IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 E), ?_, ?_⟩
  · exact Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E hne
  · intro P hP hpP
    rw [IsDedekindDomain.mem_primesOverFinset_iff hne]
    refine ⟨hP.isPrime, ⟨?_⟩⟩
    refine Ideal.IsMaximal.eq_of_le hmax ?_ ?_
    · exact (Ideal.comap_ne_top _ hP.ne_top)
    · rw [Ideal.span_le]
      simpa using hpP
end Formalism.SLP.P.CountO
