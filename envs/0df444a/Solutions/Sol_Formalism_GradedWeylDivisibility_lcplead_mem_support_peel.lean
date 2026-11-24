-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcplead_mem_support_peel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:12.951864+00:00
-- url     : https://prove2.me/submissions/9a09ce65-feeb-4fbb-a9b5-7a18fe46f52a

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCpleadLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped MonomialOrder
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (a0 : Fin r) (k : ℕ) {g : MvPolynomial (Fin r × Fin n) B}
    {p : Fin r × Fin n →₀ ℕ} (hp : p ∈ (peel l j a0 k g).support) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ p = (m.erase (a0, l)).erase (a0, j) := by
  classical
  unfold peel at hp
  obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hp)
  rw [Finset.mem_filter] at hm
  exact ⟨m, hm.1, hm.2, Finset.mem_singleton.mp (support_monomial_subset hpm)⟩
end Formalism.GradedWeylDivisibility
