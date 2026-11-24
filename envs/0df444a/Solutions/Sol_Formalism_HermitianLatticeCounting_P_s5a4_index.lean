-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:53.825342+00:00
-- url     : https://prove2.me/submissions/8b8a5ef2-d45f-49ab-8767-f7e93495cb0a

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_prime_unique
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_primes_over

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (K : Type) [Field K] [NumberField K] :
    ∃ ι : Ideal (𝓞 K) → Fin (finrank ℚ K), ∀ p : ℕ, p.Prime → ∀ Q Q' : Ideal (𝓞 K),
      Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → ι Q = ι Q' → Q = Q' := by
  classical
  have hn : 0 < finrank ℚ K := finrank_pos
  have h1 : ∀ p : ℕ, ∃ f : Ideal (𝓞 K) → Fin (finrank ℚ K), p.Prime → ∀ Q Q' : Ideal (𝓞 K),
      Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → f Q = f Q' → Q = Q' := by
    intro p
    by_cases hp : p.Prime
    · obtain ⟨s, hs, hmem⟩ := s5a4_primes_over (K := K) p hp
      refine ⟨fun Q => if h : Q ∈ s then Fin.castLE hs (s.equivFin ⟨Q, h⟩) else ⟨0, hn⟩, ?_⟩
      intro _ Q Q' hQ hQ' hpQ hpQ' he
      simp only [dif_pos (hmem Q hQ hpQ), dif_pos (hmem Q' hQ' hpQ')] at he
      have := s.equivFin.injective (Fin.castLE_injective hs he)
      exact congrArg Subtype.val this
    · exact ⟨fun _ => ⟨0, hn⟩, fun h => absurd h hp⟩
  choose f hf using h1
  let π : Ideal (𝓞 K) → ℕ := fun Q => if h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q then h.choose else 0
  have hπ : ∀ (Q : Ideal (𝓞 K)) (p : ℕ), Q.IsPrime → p.Prime → (p : 𝓞 K) ∈ Q → π Q = p := by
    intro Q p hQ hp hpQ
    have h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q := ⟨p, hp, hpQ⟩
    simp only [π, dif_pos h]
    exact s5a4_prime_unique Q hQ _ _ h.choose_spec.1 hp h.choose_spec.2 hpQ
  refine ⟨fun Q => f (π Q) Q, ?_⟩
  intro p hp Q Q' hQ hQ' hpQ hpQ' he
  simp only [hπ Q p hQ hp hpQ, hπ Q' p hQ' hp hpQ'] at he
  exact hf p hp Q Q' hQ hQ' hpQ hpQ' he
end Formalism.HermitianLatticeCounting.P
