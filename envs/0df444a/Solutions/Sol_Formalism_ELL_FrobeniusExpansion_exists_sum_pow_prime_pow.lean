-- Prove2me | solution 1 for Formalism.ELL.FrobeniusExpansion.exists_sum_pow_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:44.812801+00:00
-- url     : https://prove2.me/submissions/f5f05af7-ae8d-456b-86f0-1df82e115eb4

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsSumPowPrimePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.G
open Formalism.ELL.FrobeniusExpansion
namespace Formalism.ELL.FrobeniusExpansion
theorem _root_.solution {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → A) (n : ℕ) :
    ∃ r : A, (∑ i ∈ s, f i) ^ (p ^ n) = ∑ i ∈ s, f i ^ (p ^ n) + (p : A) * r := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp [zero_pow (pow_ne_zero n hp.ne_zero)]
  | insert a s ha ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hp (f a) (∑ i ∈ s, f i) n
    refine ⟨f a * (∑ i ∈ s, f i) * r' + r, ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]
    ring
end Formalism.ELL.FrobeniusExpansion
