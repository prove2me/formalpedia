-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lctwo_le_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:48.297174+00:00
-- url     : https://prove2.me/submissions/5b131614-033c-4c3c-8ca6-7d354297fcc8

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TwoColumn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
private theorem apply_mul_le_weight_apply {σ : Type*} (w : σ → (σ →₀ ℕ)) (d : σ →₀ ℕ) (v x : σ) :
    d v * w v x ≤ Finsupp.weight w d x := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul]
  by_cases hv : v ∈ d.support
  · exact Finset.single_le_sum (f := fun i => d i * w i x) (fun i _ => Nat.zero_le _) hv
  · have h0 : d v = 0 := by
      by_contra h
      exact hv (Finsupp.mem_support_iff.mpr h)
    rw [h0, zero_mul]
    exact Nat.zero_le _
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} {l j : Fin n} (hlj : l ≠ j) (d : Fin r × Fin n →₀ ℕ) (b : Fin r) :
    d (b, l) ≤ Finsupp.weight (pairW l j) d (b, l) ∧ d (b, j) ≤ Finsupp.weight (pairW l j) d (b, l) := by
  have hl : pairW (r := r) l j (b, l) = Finsupp.single (b, l) 1 := by
    simp [pairW, hlj]
  have hj : pairW (r := r) l j (b, j) = Finsupp.single (b, l) 1 := by
    simp [pairW]
  constructor
  · have h := apply_mul_le_weight_apply (pairW l j) d (b, l) (b, l)
    rwa [hl, Finsupp.single_eq_same, mul_one] at h
  · have h := apply_mul_le_weight_apply (pairW l j) d (b, j) (b, l)
    rwa [hj, Finsupp.single_eq_same, mul_one] at h
end Formalism.GradedWeylDivisibility
