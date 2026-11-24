-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:49.592673+00:00
-- url     : https://prove2.me/submissions/ed284a17-ab12-488a-a685-2a180acb89af

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_prime_norm

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (ι : Ideal (𝓞 K) → Fin (finrank ℚ K))
    (hι : ∀ p : ℕ, p.Prime → ∀ Q Q' : Ideal (𝓞 K),
      Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → ι Q = ι Q' → Q = Q')
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (p k : ℕ) (hp : p.Prime) (hpP : (p : 𝓞 K) ∈ P)
    (hk : Ideal.absNorm P = p ^ k) (s : Multiset (Ideal (𝓞 K)))
    (hs : ∀ Q ∈ s, Q.IsPrime ∧ Q ≠ ⊥) [DecidableEq (Ideal (𝓞 K))] :
    (((s.filter (fun Q => ι Q = ι P)).map Ideal.absNorm).prod).factorization p =
      k * s.count P := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons Q s ih =>
    have ih' := ih (fun Q' h => hs Q' (Multiset.mem_cons_of_mem h))
    obtain ⟨hQ, hQ0⟩ := hs Q (Multiset.mem_cons_self Q s)
    by_cases hi : ι Q = ι P
    · rw [Multiset.filter_cons_of_pos (p := fun Q => ι Q = ι P) s hi, Multiset.map_cons, Multiset.prod_cons]
      have hN0 : Ideal.absNorm Q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hQ0
      have hpr0 : ((s.filter (fun Q => ι Q = ι P)).map Ideal.absNorm).prod ≠ 0 := by
        apply Multiset.prod_ne_zero
        intro h0
        obtain ⟨Q', hQ', h0'⟩ := Multiset.mem_map.mp h0
        exact (hs Q' (Multiset.mem_cons_of_mem (Multiset.mem_filter.mp hQ').1)).2
          (Ideal.absNorm_eq_zero_iff.mp h0')
      rw [Nat.factorization_mul hN0 hpr0, Finsupp.add_apply, ih']
      by_cases hQP : Q = P
      · subst hQP
        rw [Multiset.count_cons_self, hk, hp.factorization_pow, Finsupp.single_eq_same]; ring
      · obtain ⟨q, j, hq, _, _, hqQ, hj⟩ := s5a4_prime_norm Q hQ hQ0
        have hqp : q ≠ p := by
          rintro rfl
          exact hQP (hι q hq Q P hQ hP hqQ hpP hi)
        rw [Multiset.count_cons_of_ne (Ne.symm hQP), hj, hq.factorization_pow,
          Finsupp.single_eq_of_ne (Ne.symm hqp), zero_add]
    · have hQP : Q ≠ P := fun h => hi (by rw [h])
      rw [Multiset.filter_cons_of_neg (p := fun Q => ι Q = ι P) s hi, Multiset.count_cons_of_ne (Ne.symm hQP), ih']
end Formalism.HermitianLatticeCounting.P
