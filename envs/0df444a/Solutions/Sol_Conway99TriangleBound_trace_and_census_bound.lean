-- Prove2me | solution 1 for Conway99TriangleBound.trace_and_census_bound
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T01:50:23.932016+00:00
-- url     : https://prove2.me/submissions/0f0ae446-07c6-479b-be27-eea5839d98ee

import Mathlib

set_option autoImplicit false

/-! A conditional aggregate lower bound for triangle traces and the associated
prism census. All trace, frame, divisibility, sum, and census hypotheses are
kept explicit. -/

open Finset

/-- If 231 trace values obey the stated frame floor and divisibility condition,
and their sum and prism census have the specified values, then the aggregate
defect is at least 858 and the prism count is at most 1100. -/
theorem solution {T : Type*} [Fintype T]
    (traceSq : T → ℤ) (delta prisms : ℕ)
    (hcard : Fintype.card T = 231)
    (hframe : ∀ t, 396 ≤ 7 * traceSq t)
    (hfour : ∀ t, 4 ∣ traceSq t)
    (hsum : (∑ t : T, traceSq t) = 84 * (delta : ℤ) - 58212)
    (hcensus : delta + 3 * prisms = 4158) :
    858 ≤ delta ∧ prisms ≤ 1100 := by
  have htrace (t : T) : 60 ≤ traceSq t := by
    obtain ⟨k, hk⟩ := hfour t
    have hf := hframe t
    rw [hk] at hf ⊢
    omega
  have hbound : (∑ _t : T, (60 : ℤ)) ≤ ∑ t : T, traceSq t :=
    Finset.sum_le_sum (fun t _ => htrace t)
  have hconstant : (∑ _t : T, (60 : ℤ)) = 231 * 60 := by
    simp [hcard]
  rw [hconstant, hsum] at hbound
  have hdeltaZ : (858 : ℤ) ≤ (delta : ℤ) := by omega
  have hdelta : 858 ≤ delta := by exact_mod_cast hdeltaZ
  have hprism : prisms ≤ 1100 := by omega
  exact ⟨hdelta, hprism⟩

#print axioms solution
