-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcplead_weight_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:10:22.247089+00:00
-- url     : https://prove2.me/submissions/d38b5f01-e609-4170-b33e-59fef6d33c63

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCpleadLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
open scoped MonomialOrder
noncomputable section
namespace Formalism.GradedWeylDivisibility
private lemma pairW_apply {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) (b : Fin r)
    (t : Fin n) :
    pairW l j v (b, t) = if v.2 = j then (if (v.1, l) = (b, t) then 1 else 0)
      else (if v = (b, t) then 1 else 0) := by
  classical
  unfold pairW
  split_ifs <;> simp_all [Finsupp.single_apply]
section
variable {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n}
end
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial
open scoped MonomialOrder
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (d : Fin r × Fin n →₀ ℕ)
    (b : Fin r) (t : Fin n) :
    Finsupp.weight (pairW l j) d (b, t) =
      if t = l then d (b, l) + d (b, j) else if t = j then 0 else d (b, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, pairW_apply, smul_eq_mul]
  split_ifs with h1 h2
  · subst h1
    rw [Fintype.sum_eq_add (b, t) (b, j) (by simp [hlj])]
    · simp [hlj]
    · rintro ⟨a, s⟩ ⟨ha1, ha2⟩
      by_cases hs : s = j <;> simp_all [Prod.ext_iff]
  · subst h2
    refine Finset.sum_eq_zero fun x _ => ?_
    obtain ⟨a, s⟩ := x
    by_cases hs : s = t <;> simp_all [Prod.ext_iff]
  · rw [Fintype.sum_eq_single (b, t)]
    · simp [h2]
    · rintro ⟨a, s⟩ hx
      have h1' : l ≠ t := Ne.symm h1
      by_cases hs : s = j <;> simp_all [Prod.ext_iff]
end Formalism.GradedWeylDivisibility
