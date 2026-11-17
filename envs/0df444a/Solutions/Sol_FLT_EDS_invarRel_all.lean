-- Prove2me | solution 1 for FLT.EDS.invarRel_all
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:44.611744+00:00
-- url     : https://prove2.me/submissions/4c25f147-98c0-40ba-b4c8-d1bb89eaaae0

import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_WardConservation
import Definitions.Def_WardInvariant
import Theorems.Thm_FLT_EDS_normEDS_conservation
import Definitions.Def_WardSomos

/-! Proofs of the lemmas stated in `Theorems.Thm_EDS_SingleIndexInvariant` and their helpers. -/

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- Base cases: `n = 0, 1` (both sides vanish) and `n = 2`. -/
public lemma invarRel_zero (b c d : R) : InvarRel b c d 0 := by
  unfold InvarRel Nseq Dseq
  simp [normEDS_zero, normEDS_one, normEDS_two, normEDS_neg]

public lemma invarRel_one (b c d : R) : InvarRel b c d 1 := by
  unfold InvarRel Nseq Dseq
  simp [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_neg]

public lemma invarRel_two (b c d : R) : InvarRel b c d 2 := by
  unfold InvarRel Nseq Dseq
  norm_num [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_four]
  ring

/-- Inductive step (multiplied form, holds over any `CommRing`): from `InvarRel n`,
`D_n · (InvarRel n+1)` vanishes. Cofactors `c · conservation + D_{n+1} · (IH)`, an atom-level ring
identity (no unfolding of `Nseq`/`Dseq` needed). The final `InvarRel (n+1)` is got by cancelling
`D_n` over a domain where `D_n ≠ 0` (e.g. the division-polynomial setting, `preΨ` nonvanishing via
`Mathlib …DivisionPolynomial.Degree`). -/
public lemma invarRel_step_mul (b c d : R) (n : ℤ) (hn : InvarRel b c d n) :
    Dseq b c d n * (c * Nseq b c d (n+1) - (d + b ^ 4) * Dseq b c d (n+1)) = 0 := by
  have hcons := normEDS_conservation b c d n
  unfold InvarRel at hn
  linear_combination c * hcons + Dseq b c d (n+1) * hn

/-- **Full single-index invariant.** Over a domain where the `normEDS` values do not vanish
(e.g. the division-polynomial setting — `preΨ` nonvanishing via Mathlib's degree lemmas),
`InvarRel n` holds for every `n`. Proof: `Int` induction off the base cases and `invarRel_step_mul`,
cancelling `D_n ≠ 0`; negative `n` by the `Nseq`/`Dseq` sign symmetry. -/
theorem _root_.solution [IsDomain R] (b c d : R)
    (hne : ∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0) (n : ℤ) : InvarRel b c d n := by
  have hge2 : ∀ m : ℤ, 2 ≤ m → InvarRel b c d m := by
    intro m hm
    induction m, hm using Int.le_induction with
    | base => exact invarRel_two b c d
    | succ k hk ih =>
      have hstep := invarRel_step_mul b c d k ih
      have hDk : Dseq b c d k ≠ 0 := by
        unfold Dseq
        exact mul_ne_zero (mul_ne_zero (hne (k+1) (by omega)) (hne k (by omega)))
          (hne (k-1) (by omega))
      unfold InvarRel
      have := (mul_eq_zero.mp hstep).resolve_left hDk
      linear_combination this
  have hpos : ∀ m : ℤ, 0 ≤ m → InvarRel b c d m := by
    intro m hm
    rcases lt_or_ge m 2 with h2 | h2
    · interval_cases m
      · exact invarRel_zero b c d
      · exact invarRel_one b c d
    · exact hge2 m h2
  rcases lt_or_ge n 0 with h | h
  · have hsym : InvarRel b c d (-n) := hpos (-n) (by omega)
    have hN : Nseq b c d (-n) = - Nseq b c d n := by
      unfold Nseq
      rw [show -n+2 = -(n-2) by ring, show -n-1 = -(n+1) by ring, show -n+1 = -(n-1) by ring,
        show -n-2 = -(n+2) by ring, normEDS_neg, normEDS_neg, normEDS_neg, normEDS_neg, normEDS_neg]
      ring
    have hD : Dseq b c d (-n) = - Dseq b c d n := by
      unfold Dseq
      rw [show -n+1 = -(n-1) by ring, show -n-1 = -(n+1) by ring, normEDS_neg, normEDS_neg, normEDS_neg]
      ring
    unfold InvarRel at hsym ⊢
    rw [hN, hD] at hsym
    linear_combination -hsym
  · exact hpos n h

end FLT.EDS
