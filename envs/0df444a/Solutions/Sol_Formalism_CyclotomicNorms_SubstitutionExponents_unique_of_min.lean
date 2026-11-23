-- Prove2me | solution 1 for Formalism.CyclotomicNorms.SubstitutionExponents.unique_of_min
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:23.711825+00:00
-- url     : https://prove2.me/submissions/5b612076-9a60-409d-b9a3-f824bfe6ffe6

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
import Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_sum_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.SubstitutionExponents
variable {r : ℕ}
namespace Formalism.CyclotomicNorms.SubstitutionExponents
theorem _root_.solution (n : Fin r → ℕ) (a : Fin r →₀ ℕ)
    (hn : ∀ j, ∑ i ∈ univ.filter (· < j), a i * n i < n j)
    (d : Fin r →₀ ℕ) (hmin : ¬ revLex d a) (hw : weight n d = weight n a) : d = a := by
  classical
  by_contra hne
  have hS : (univ.filter fun i => d i ≠ a i).Nonempty := by
    by_contra h
    apply hne
    ext i
    by_contra hi
    exact h ⟨i, by simp [hi]⟩
  set j := (univ.filter fun i => d i ≠ a i).max' hS with hj
  have hdj : d j ≠ a j := by
    have := Finset.max'_mem _ hS
    rw [← hj] at this
    simpa using this
  have habove : ∀ i, j < i → d i = a i := by
    intro i hi
    by_contra h
    have : i ≤ j := Finset.le_max' _ i (by simp [h])
    exact absurd hi (not_lt.2 this)
  have hlt : a j < d j := by
    rcases lt_or_gt_of_ne hdj with h | h
    · exact absurd ⟨j, fun i hi => habove i hi, h⟩ hmin
    · exact h
  have e1 := sum_split (fun i => d i * n i) j
  have e2 := sum_split (fun i => a i * n i) j
  have e3 : ∑ i ∈ univ.filter (j < ·), d i * n i = ∑ i ∈ univ.filter (j < ·), a i * n i :=
    Finset.sum_congr rfl (fun i hi => by rw [habove i (by simpa using hi)])
  have h4 := hn j
  have h5 : (a j + 1) * n j ≤ d j * n j := Nat.mul_le_mul_right _ hlt
  rw [add_mul, one_mul] at h5
  unfold weight at hw
  rw [e1, e2, e3] at hw
  omega
end Formalism.CyclotomicNorms.SubstitutionExponents
