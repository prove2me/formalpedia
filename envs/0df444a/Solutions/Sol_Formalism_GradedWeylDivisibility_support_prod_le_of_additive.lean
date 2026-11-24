-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.support_prod_le_of_additive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:16.573796+00:00
-- url     : https://prove2.me/submissions/232fe31a-45f6-474a-b41f-94fc72615179

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {σ ι R : Type*} [CommSemiring R] [DecidableEq ι] [DecidableEq σ]
    (F : (σ →₀ ℕ) → ℕ) (hF0 : F 0 = 0) (hFa : ∀ a b, F (a + b) = F a + F b)
    (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ι → ℕ)
    (hb : ∀ i ∈ s, ∀ m ∈ (f i).support, F m ≤ b i) :
    ∀ m ∈ (∏ i ∈ s, f i).support, F m ≤ ∑ i ∈ s, b i := by
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.prod_empty, mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp [hF0]
    · exact absurd rfl hm
  | insert i s hi ih =>
    intro m hm
    rw [Finset.prod_insert hi] at hm
    obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    rw [hFa, Finset.sum_insert hi]
    exact Nat.add_le_add (hb i (mem_insert_self _ _) a ha)
      (ih (fun j hj => hb j (mem_insert_of_mem hj)) c hc)
end Formalism.GradedWeylDivisibility
